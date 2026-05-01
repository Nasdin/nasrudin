//! `GET /api/search/concept?q=…` — natural-language search across the
//! corpus. Returns both verified theorems and pending conjectures so the
//! researcher can see in-flight work alongside completed proofs.
//!
//! Two parallel signals are merged:
//!   1. **Embedding nearest-neighbours** (verified-only — the index is
//!      built from `Verified` rows in Phase B). Score = `1 - distance`,
//!      so 1.0 is a perfect hit and 0.0 is opposite.
//!   2. **PG `ILIKE` substring match** (any non-rejected status). Score
//!      = a shorter-match-better heuristic so a hit on a 10-char
//!      statement scores higher than the same needle in a 200-char one.
//!
//! Hits are merged on `theorem_id`, scores combined (max), and the top
//! `limit` returned ordered by combined score.

use std::collections::HashMap;
use std::sync::Arc;

use axum::{
    extract::{Query, State},
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use serde::{Deserialize, Serialize};

use crate::state::AppState;

#[derive(Deserialize)]
pub struct ConceptQuery {
    pub q: String,
    #[serde(default)]
    pub limit: Option<u64>,
    /// `true` (default) → include `Pending` rows (conjectures-in-flight).
    /// `false` → verified-only.
    #[serde(default = "default_include_pending")]
    pub include_pending: bool,
}

fn default_include_pending() -> bool {
    true
}

#[derive(Serialize)]
pub struct ConceptHit {
    pub theorem_id: String,
    pub canonical_statement: String,
    pub latex: Option<String>,
    pub domain: String,
    pub status: String,
    pub depth: Option<i32>,
    /// Combined score in [0, 1]. Higher is better.
    pub score: f32,
    /// Which signal flagged it: "embed" | "text" | "both".
    pub source: &'static str,
}

#[derive(Serialize)]
pub struct ConceptSearchResponse {
    pub query: String,
    pub hits: Vec<ConceptHit>,
    pub took_ms: u128,
    pub embed_available: bool,
}

const MAX_LIMIT: u64 = 100;
const DEFAULT_LIMIT: u64 = 20;

pub async fn concept_search(
    State(state): State<Arc<AppState>>,
    Query(params): Query<ConceptQuery>,
) -> Response {
    let started = std::time::Instant::now();
    let q = params.q.trim();
    if q.is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({"error": "empty_query"})),
        )
            .into_response();
    }
    let limit = params.limit.unwrap_or(DEFAULT_LIMIT).min(MAX_LIMIT).max(1);
    let Some(pg) = state.pg.as_ref() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({"error": "pg_unavailable"})),
        )
            .into_response();
    };

    // Map of theorem_id (hex) → (combined score, source, partial hit data).
    let mut merged: HashMap<String, ConceptHit> = HashMap::new();

    // ── Signal 1: embedding nearest-neighbour over the verified corpus.
    let embed_available = state.embed.is_some() && state.embedder.is_some();
    if let (Some(index), Some(embedder)) = (state.embed.as_ref(), state.embedder.as_ref()) {
        let k = (limit * 2).min(MAX_LIMIT) as usize;
        if let Ok(hits) = index.nearest_text(embedder, q, k) {
            // Batch-fetch all rows in one PG round-trip instead of N. The
            // embedding index returns up to `2*limit` neighbours; resolving
            // each one individually was O(k) round-trips before.
            let ids: Vec<Vec<u8>> = hits.iter().map(|h| h.theorem_id.to_vec()).collect();
            let rows = nasrudin_pg::query::theorems::list_by_ids(pg, &ids)
                .await
                .unwrap_or_default();
            let row_by_id: HashMap<Vec<u8>, _> =
                rows.into_iter().map(|m| (m.id.clone(), m)).collect();

            // Cosine distance ∈ [0, 2]; convert to [0, 1] similarity.
            for h in hits {
                let Some(row) = row_by_id.get(h.theorem_id.as_slice()) else {
                    continue;
                };
                let id_hex = h
                    .theorem_id
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect::<String>();
                let score = (1.0 - (h.distance / 2.0)).clamp(0.0, 1.0);
                merged.insert(
                    id_hex.clone(),
                    ConceptHit {
                        theorem_id: id_hex,
                        canonical_statement: row.canonical_statement.clone(),
                        latex: row.latex.clone(),
                        domain: row.domain.clone(),
                        status: row.status.clone(),
                        depth: row.depth,
                        score,
                        source: "embed",
                    },
                );
            }
        }
    }

    // ── Signal 2: ILIKE text search (any non-rejected status).
    if let Ok(rows) =
        nasrudin_pg::query::search::list_by_text(pg, q, limit, params.include_pending).await
    {
        for row in rows {
            let id_hex = row.id.iter().map(|b| format!("{b:02x}")).collect::<String>();
            // Shorter-match-better: q.len() / canonical.len(), capped at 1.
            let denom = row.canonical_statement.len().max(q.len()).max(1) as f32;
            let text_score = (q.len() as f32 / denom).clamp(0.0, 1.0);
            merged
                .entry(id_hex.clone())
                .and_modify(|existing| {
                    existing.score = existing.score.max(text_score);
                    existing.source = "both";
                })
                .or_insert_with(|| ConceptHit {
                    theorem_id: id_hex,
                    canonical_statement: row.canonical_statement.clone(),
                    latex: row.latex.clone(),
                    domain: row.domain.clone(),
                    status: row.status.clone(),
                    depth: row.depth,
                    score: text_score,
                    source: "text",
                });
        }
    }

    let mut hits: Vec<ConceptHit> = merged.into_values().collect();
    hits.sort_by(|a, b| b.score.partial_cmp(&a.score).unwrap_or(std::cmp::Ordering::Equal));
    hits.truncate(limit as usize);

    Json(ConceptSearchResponse {
        query: q.to_string(),
        hits,
        took_ms: started.elapsed().as_millis(),
        embed_available,
    })
    .into_response()
}
