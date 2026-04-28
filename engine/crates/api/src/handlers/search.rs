//! `POST /api/search` — the Einstein search endpoint.
//!
//! Three-tier flow:
//!   1. **Exact** — parse the input, AC-canonicalize, look up by hash. Sub-10ms.
//!   2. **Unify** — narrow candidates by filters, then `match_expr` each
//!      against the parsed pattern. Pattern variables are any `Var` in the
//!      input.
//!   3. **Near-miss** — same candidates ranked by token Levenshtein over the
//!      AC-canonical string + dimensional Hamming + axiom-set Jaccard.
//!
//! When `input_format == "form"` no parser runs; we go straight to a
//! filter-driven candidate list (Tier 2 without unification).

use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use nasrudin_core::{Expr, canonical_ac_hash, canonical_ac_string, parse};
use nasrudin_derive::rewrite::match_expr;
use nasrudin_pg::entity::theorems;
use nasrudin_pg::query::search as pg_search;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::state::AppState;

#[derive(Deserialize, Debug)]
pub struct SearchRequest {
    /// Free-form expression text. Ignored when `input_format == "form"`.
    #[serde(default)]
    pub input: String,
    /// One of `"latex"`, `"math"`, `"sexpr"`, `"form"`.
    pub input_format: String,
    /// Optional structured filters; all fields default to "no constraint".
    #[serde(default)]
    pub filters: Filters,
    /// Result cap. Server enforces `limit <= 100`; defaults to 20.
    #[serde(default)]
    pub limit: Option<u64>,
}

#[derive(Deserialize, Default, Debug)]
pub struct Filters {
    pub domain: Option<String>,
    /// 7-vector matching `Dimension` (length, mass, time, current, temp,
    /// amount, luminosity).
    pub dimension: Option<Vec<i32>>,
    /// Axioms that MUST appear in `axioms_used`.
    #[serde(default)]
    pub axioms_required: Vec<String>,
    pub max_depth: Option<i32>,
}

#[derive(Serialize, Debug)]
pub struct SearchResponse {
    pub tier: Tier,
    pub matches: Vec<MatchItem>,
    pub took_ms: u128,
    pub parse_error: Option<String>,
    /// Echoes the filter set the server actually applied (after defaults).
    pub applied_filters: Filters,
}

// Filters echoed back in the response: same shape as the inbound,
// serialize manually so we don't have to drop the inbound `Deserialize`.
impl Serialize for Filters {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut st = s.serialize_struct("Filters", 4)?;
        st.serialize_field("domain", &self.domain)?;
        st.serialize_field("dimension", &self.dimension)?;
        st.serialize_field("axioms_required", &self.axioms_required)?;
        st.serialize_field("max_depth", &self.max_depth)?;
        st.end()
    }
}

#[derive(Serialize, Clone, Copy, Debug)]
#[serde(rename_all = "snake_case")]
pub enum Tier {
    Exact,
    Unify,
    NearMiss,
    Empty,
}

#[derive(Serialize, Debug)]
pub struct MatchItem {
    pub id: String,
    pub canonical_statement: String,
    pub statement_latex: Option<String>,
    pub domain: String,
    pub dimension: Option<Vec<i32>>,
    pub depth: Option<i32>,
    pub axioms_used: Vec<String>,
    pub r#match: MatchKind,
    pub lean_url: String,
    pub proof_url: String,
}

#[derive(Serialize, Debug)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum MatchKind {
    Exact,
    Unify {
        bindings: serde_json::Map<String, serde_json::Value>,
    },
    NearMiss {
        score: f32,
        token_distance: u32,
        dim_hamming: u32,
        axiom_jaccard: f32,
    },
}

const HARD_LIMIT: u64 = 100;
const CANDIDATE_FETCH_CAP: u64 = 500;
const NEAR_MISS_SCORE_FLOOR: f32 = 0.65;

pub async fn search(
    State(state): State<Arc<AppState>>,
    Json(req): Json<SearchRequest>,
) -> impl IntoResponse {
    let started = std::time::Instant::now();
    let limit = req.limit.unwrap_or(20).min(HARD_LIMIT);

    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({ "error": "pg_unavailable" })),
            )
                .into_response();
        }
    };

    // Parse the input (unless `form` mode).
    let (pattern, parse_error) = match req.input_format.as_str() {
        "form" => (None, None),
        "sexpr" => parse_or_err(parse::parse_sexpr(&req.input)),
        "math" => parse_or_err(parse::parse_simple(&req.input)),
        "latex" => parse_or_err(parse::parse_latex(&req.input)),
        other => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({
                    "error": format!("unknown input_format `{other}`")
                })),
            )
                .into_response();
        }
    };

    if let Some(err) = parse_error.as_ref() {
        return (
            StatusCode::OK,
            Json(SearchResponse {
                tier: Tier::Empty,
                matches: vec![],
                took_ms: started.elapsed().as_millis(),
                parse_error: Some(err.clone()),
                applied_filters: req.filters,
            }),
        )
            .into_response();
    }

    // Tier 1 — AC-exact lookup (skip in form mode).
    if let Some(p) = pattern.as_ref() {
        let hash = canonical_ac_hash(p);
        match pg_search::find_by_ac_hash(pg, &hash).await {
            Ok(Some(row)) => {
                return ok(SearchResponse {
                    tier: Tier::Exact,
                    matches: vec![row_to_match(row, MatchKind::Exact)],
                    took_ms: started.elapsed().as_millis(),
                    parse_error: None,
                    applied_filters: req.filters,
                });
            }
            Ok(None) => {}
            Err(e) => {
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(serde_json::json!({ "error": e.to_string() })),
                )
                    .into_response();
            }
        }
    }

    // Tier 2 — narrow by filters, then unify (or just return filter results in form mode).
    let filter = pg_search::CandidateFilter {
        domain: req.filters.domain.clone(),
        dimension: req.filters.dimension.clone(),
        axioms_required: req.filters.axioms_required.clone(),
        max_depth: req.filters.max_depth,
    };
    let candidates = match pg_search::candidates(pg, &filter, CANDIDATE_FETCH_CAP).await {
        Ok(rows) => rows,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };

    if candidates.is_empty() {
        return ok(SearchResponse {
            tier: Tier::Empty,
            matches: vec![],
            took_ms: started.elapsed().as_millis(),
            parse_error: None,
            applied_filters: req.filters,
        });
    }

    if let Some(p) = pattern.as_ref() {
        // Try unification first.
        let mut unify_hits = Vec::new();
        for cand in &candidates {
            let Some(parsed) = parse::parse_sexpr(&cand.canonical_statement).ok() else {
                continue;
            };
            if let Some(bindings) = match_expr(p, &parsed) {
                let bindings_json = bindings
                    .into_iter()
                    .map(|(k, v)| (k, serde_json::Value::String(v.to_canonical())))
                    .collect();
                unify_hits.push(row_to_match(
                    cand.clone(),
                    MatchKind::Unify { bindings: bindings_json },
                ));
                if unify_hits.len() as u64 >= limit {
                    break;
                }
            }
        }
        if !unify_hits.is_empty() {
            return ok(SearchResponse {
                tier: Tier::Unify,
                matches: unify_hits,
                took_ms: started.elapsed().as_millis(),
                parse_error: None,
                applied_filters: req.filters,
            });
        }

        // Tier 3 — near-miss ranking
        let pattern_canon = canonical_ac_string(p);
        let pattern_axioms: std::collections::BTreeSet<&str> = req
            .filters
            .axioms_required
            .iter()
            .map(|s| s.as_str())
            .collect();
        let pattern_dim = req.filters.dimension.as_deref();
        let mut scored: Vec<(f32, u32, u32, f32, theorems::Model)> = candidates
            .into_iter()
            .map(|c| {
                let cand_canon = ac_string_or_raw(&c.canonical_statement);
                let token_dist = token_levenshtein(&pattern_canon, &cand_canon);
                let dim_h = match (pattern_dim, c.dimension.as_deref()) {
                    (Some(a), Some(b)) => dim_hamming(a, b),
                    _ => 7, // missing dimension — treat as max distance
                };
                let cand_ax: std::collections::BTreeSet<&str> =
                    c.axioms_used.iter().map(|s| s.as_str()).collect();
                let jacc = jaccard_distance(&pattern_axioms, &cand_ax);
                let score = composite_score(token_dist, dim_h, jacc);
                (score, token_dist, dim_h, jacc, c)
            })
            .filter(|(s, _, _, _, _)| *s <= NEAR_MISS_SCORE_FLOOR)
            .collect();
        scored.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        scored.truncate(limit as usize);

        let matches: Vec<MatchItem> = scored
            .into_iter()
            .map(|(score, td, dh, jacc, row)| {
                row_to_match(
                    row,
                    MatchKind::NearMiss {
                        score,
                        token_distance: td,
                        dim_hamming: dh,
                        axiom_jaccard: jacc,
                    },
                )
            })
            .collect();

        let tier = if matches.is_empty() { Tier::Empty } else { Tier::NearMiss };
        return ok(SearchResponse {
            tier,
            matches,
            took_ms: started.elapsed().as_millis(),
            parse_error: None,
            applied_filters: req.filters,
        });
    }

    // Form-only mode: return the filter results directly as Unify-with-empty-bindings.
    let matches: Vec<MatchItem> = candidates
        .into_iter()
        .take(limit as usize)
        .map(|row| {
            row_to_match(
                row,
                MatchKind::Unify { bindings: serde_json::Map::new() },
            )
        })
        .collect();
    let tier = if matches.is_empty() { Tier::Empty } else { Tier::Unify };
    ok(SearchResponse {
        tier,
        matches,
        took_ms: started.elapsed().as_millis(),
        parse_error: None,
        applied_filters: req.filters,
    })
}

fn ok(resp: SearchResponse) -> axum::response::Response {
    (StatusCode::OK, Json(resp)).into_response()
}

fn parse_or_err<E: std::fmt::Display>(
    r: Result<Expr, E>,
) -> (Option<Expr>, Option<String>) {
    match r {
        Ok(e) => (Some(e), None),
        Err(e) => (None, Some(e.to_string())),
    }
}

fn ac_string_or_raw(canonical_statement: &str) -> String {
    // The PG row stores the *syntactic* canonical (output of `to_canonical`).
    // Re-parse and re-canonicalize through the AC pipeline so distance is
    // measured on apples-to-apples; fall back to the raw string if parsing
    // fails (legacy rows).
    match parse::parse_sexpr(canonical_statement) {
        Ok(e) => canonical_ac_string(&e),
        Err(_) => canonical_statement.to_string(),
    }
}

fn token_levenshtein(a: &str, b: &str) -> u32 {
    let av: Vec<&str> = a.split_whitespace().collect();
    let bv: Vec<&str> = b.split_whitespace().collect();
    let (m, n) = (av.len(), bv.len());
    if m == 0 {
        return n as u32;
    }
    if n == 0 {
        return m as u32;
    }
    let mut prev: Vec<u32> = (0..=n as u32).collect();
    let mut cur = vec![0u32; n + 1];
    for i in 1..=m {
        cur[0] = i as u32;
        for j in 1..=n {
            let cost = if av[i - 1] == bv[j - 1] { 0 } else { 1 };
            cur[j] = (cur[j - 1] + 1)
                .min(prev[j] + 1)
                .min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[n]
}

fn dim_hamming(a: &[i32], b: &[i32]) -> u32 {
    let len = a.len().max(b.len());
    let mut h = 0u32;
    for i in 0..len {
        let av = a.get(i).copied().unwrap_or(0);
        let bv = b.get(i).copied().unwrap_or(0);
        if av != bv {
            h += 1;
        }
    }
    h
}

fn jaccard_distance<T: Ord>(
    a: &std::collections::BTreeSet<T>,
    b: &std::collections::BTreeSet<T>,
) -> f32 {
    let inter = a.intersection(b).count() as f32;
    let union = a.union(b).count() as f32;
    if union == 0.0 {
        0.0
    } else {
        1.0 - inter / union
    }
}

/// Composite [0, 1] score, lower is better.
///
/// Token Levenshtein dominates (60% weight) since structure is the strongest
/// search signal; dimension and axiom-set distances each contribute 20%.
fn composite_score(token_dist: u32, dim_h: u32, axiom_jacc: f32) -> f32 {
    // Normalize token distance with a soft cap of 50 tokens.
    let td_norm = (token_dist as f32 / 50.0).min(1.0);
    let dh_norm = (dim_h as f32 / 7.0).min(1.0);
    0.6 * td_norm + 0.2 * dh_norm + 0.2 * axiom_jacc
}

fn row_to_match(row: theorems::Model, kind: MatchKind) -> MatchItem {
    let id_hex = hex::encode(&row.id);
    let hash_hex = hex::encode(&row.canonical_hash);
    MatchItem {
        canonical_statement: row.canonical_statement,
        statement_latex: row.latex,
        domain: row.domain,
        dimension: row.dimension,
        depth: row.depth,
        axioms_used: row.axioms_used,
        r#match: kind,
        lean_url: format!("/api/theorems/{hash_hex}/lean"),
        proof_url: format!("/api/theorems/{id_hex}/proof"),
        id: id_hex,
    }
}
