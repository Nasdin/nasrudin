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

use crate::state::AppState;

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

    // Seed theorems: top-N Verified for the given domain (newest-first; the
    // pg query layer doesn't expose a fitness sort yet, so newest-first is
    // the closest stable proxy and matches `/api/theorems` semantics).
    let seed_theorems = match nasrudin_pg::query::theorems::list_verified(
        pg,
        None,
        top,
        q.domain.clone(),
    )
    .await
    {
        Ok(page) => page.items,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "error": format!("seed_query_failed: {e}")
                })),
            )
                .into_response();
        }
    };

    (
        StatusCode::OK,
        Json(serde_json::json!({
            "axioms": axioms,
            "seed_theorems": seed_theorems,
        })),
    )
        .into_response()
}
