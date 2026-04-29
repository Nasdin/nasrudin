//! `GET /api/seed` — remote-worker bootstrap endpoint (Phase 9 Task 5.3).
//!
//! Returns the in-memory axiom catalog plus the top-N highest-fitness
//! `Verified` theorems for the given domain. A Phase-10 remote worker calls
//! this once at cold start to seed its local GA population without having to
//! page the full theorem mirror.
//!
//! Shape:
//! ```json
//! {
//!   "axioms":         [{"name": "...", "statement": "...", "domain": "..."}, ...],
//!   "seed_theorems":  [<Theorem>, ...]
//! }
//! ```
//!
//! `top` is clamped to 500 to keep the response bounded.
//! When PostgreSQL is not configured, the endpoint returns `503` with
//! `error = "pg_unavailable"` for symmetry with the rest of the read API.

use axum::{
    Json,
    extract::{Query, State},
    http::StatusCode,
    response::IntoResponse,
};
use serde::Deserialize;
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::state::{AppState, SeedCacheKey};

/// How long a serialised /api/seed response stays valid in cache. The
/// AxiomStore only changes via /api/admin/reload_corpus (which busts
/// the cache) and the verified-recent index ticks roughly every chunk
/// (60s). 30s is a safe middle ground: workers polling at 60s cadence
/// hit fresh data on alternating polls.
const SEED_CACHE_TTL: Duration = Duration::from_secs(30);

#[derive(Deserialize)]
pub struct SeedQuery {
    pub domain: Option<String>,
    pub top: Option<u64>,
}

/// `GET /api/seed?domain=X&top=N` — bootstrap payload for a remote worker.
pub async fn seed(
    State(state): State<Arc<AppState>>,
    Query(q): Query<SeedQuery>,
) -> impl IntoResponse {
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
    let top = q.top.unwrap_or(50).min(500);

    // ── Cache hit fast path ───────────────────────────────────────────
    // Most workers re-poll /api/seed at chunk boundaries with the same
    // (domain, top). Skip the entire axiom-store iteration + verified-
    // recent fetch + JSON serialise if we have a fresh cached body.
    // Cache invalidation: /api/admin/reload_corpus clears the map after
    // hot-reloading the AxiomStore.
    let cache_key = SeedCacheKey {
        domain: q.domain.clone(),
        top,
    };
    if let Ok(map) = state.seed_cache.lock() {
        if let Some((generated_at, body)) = map.get(&cache_key) {
            if generated_at.elapsed() < SEED_CACHE_TTL {
                return (
                    StatusCode::OK,
                    [(axum::http::header::CONTENT_TYPE, "application/json")],
                    body.as_bytes().to_vec(),
                )
                    .into_response();
            }
        }
    }

    // Axioms from the in-memory AxiomStore. Domain filter accepts either the
    // Display form ("special_relativity") or the Rust enum name
    // ("SpecialRelativity") so callers can use whichever convention their
    // local DSL prefers.
    let domain_filter = q.domain.clone();
    let store = state.axiom_store.load();
    let axioms: Vec<serde_json::Value> = store
        .iter()
        .filter(|a| {
            domain_filter.as_ref().is_none_or(|d| {
                let dom_dbg = format!("{:?}", a.domain);
                let dom_disp = format!("{}", a.domain);
                dom_dbg == *d || dom_disp == *d
            })
        })
        .map(|a| {
            // Expr has no Display impl; serialise to JSON so a worker can
            // round-trip it back into an Expr tree. Falls back to the Rust
            // Debug form on the (unreachable) serde failure.
            let statement = serde_json::to_string(&a.statement)
                .unwrap_or_else(|_| format!("{:?}", a.statement));
            serde_json::json!({
                "name": a.name,
                "statement": statement,
                "domain": format!("{}", a.domain),
                "description": a.description,
            })
        })
        .collect();

    // Seed theorems: top-N Verified, newest-first. RocksDB-primary
    // (Task 4): the verified-at index is populated by `flip_verified`
    // every time a theorem flips to Verified, so this returns the same
    // data PG would but ~10× faster (RocksDB indexed scan vs. PG row
    // fetch). Falls back to PG when the RocksDB index is empty so
    // legacy data still surfaces during the rollout window.
    let _ = pg; // PG kept for the legacy fallback below.
    let mut seed_theorems: Vec<serde_json::Value> = Vec::new();
    // P-Task 1 firewall: workers only compose chains on top of LakeVerified
    // (kernel-confirmed) ancestors. ChainVerified theorems are
    // intentionally absent from the seed payload; they get queued for
    // lake-promotion (P-Task 2) so they eventually graduate. Without
    // this filter, a bogus theorem that passes chain replay but fails
    // lake build would silently propagate as a peer-axiom across the
    // cluster — exactly the pollution scenario cascade-reject (P-Task 3)
    // is designed to clean up *after the fact*. This filter prevents
    // pollution at the source.
    //
    // Pull a wider window than `top` from the recency index so we can
    // afford to skip ChainVerified rows without thinning the response.
    let scan_window = (top as usize).saturating_mul(8).max(top as usize);
    if let Ok(ids) = state.db.list_verified_recent_ids(scan_window) {
        for id in ids {
            if seed_theorems.len() >= top as usize {
                break;
            }
            if let Ok(Some(theorem)) = state.db.get_theorem(&id) {
                // Hard-filter: only LakeVerified theorems are eligible
                // peer-axioms.
                let lake_verified = matches!(
                    &theorem.verified,
                    nasrudin_core::VerificationStatus::Verified { tactic_used, .. }
                        if tactic_used == "lake_build"
                );
                if !lake_verified {
                    // Side effect: enqueue this ChainVerified theorem
                    // for lake promotion at priority 1 (seed-inclusion
                    // demand). The /api/seed endpoint heating up the
                    // promotion queue means workers polling create
                    // pressure to graduate the freshest theorems first.
                    if let nasrudin_core::VerificationStatus::Verified { tactic_used, .. }
                        = &theorem.verified
                    {
                        if tactic_used == "chain_replay" {
                            let _ = state.db.enqueue_lake_promotion(&id, 1);
                        }
                    }
                    continue;
                }
                if let Some(ref d) = q.domain {
                    let dom_disp = format!("{}", theorem.domain);
                    let dom_dbg = format!("{:?}", theorem.domain);
                    if dom_disp != *d && dom_dbg != *d {
                        continue;
                    }
                }
                seed_theorems.push(
                    serde_json::to_value(&theorem)
                        .unwrap_or_else(|_| serde_json::Value::Null),
                );
            }
        }
    }
    if seed_theorems.is_empty() {
        match nasrudin_pg::query::theorems::list_verified(
            pg,
            None,
            top,
            q.domain.clone(),
        )
        .await
        {
            Ok(page) => {
                seed_theorems = page
                    .items
                    .into_iter()
                    .map(|m| {
                        serde_json::to_value(&m).unwrap_or_else(|_| serde_json::Value::Null)
                    })
                    .collect();
            }
            Err(e) => {
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(serde_json::json!({
                        "error": format!("seed_query_failed: {e}")
                    })),
                )
                    .into_response();
            }
        }
    }

    let body = serde_json::json!({
        "axioms": axioms,
        "seed_theorems": seed_theorems,
    });
    let body_str = serde_json::to_string(&body)
        .unwrap_or_else(|_| r#"{"error":"serialise_failed"}"#.to_string());
    let body_arc = Arc::new(body_str);
    if let Ok(mut map) = state.seed_cache.lock() {
        map.insert(cache_key, (Instant::now(), Arc::clone(&body_arc)));
    }
    (
        StatusCode::OK,
        [(axum::http::header::CONTENT_TYPE, "application/json")],
        body_arc.as_bytes().to_vec(),
    )
        .into_response()
}
