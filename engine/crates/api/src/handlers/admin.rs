//! Admin endpoints — corpus reload, gated by `ADMIN_TOKEN`.
//!
//! `POST /api/admin/reload_corpus` rebuilds the in-memory `AxiomStore`
//! from the on-disk catalogs (`catalog.json` + `math_corpus.json`) plus
//! the hardcoded upstream postulates, runs the no-cheat audit, and
//! atomically swaps the store. Workers see the new building blocks on
//! their next `/api/seed` poll.
//!
//! Auth: `Authorization: Bearer <ADMIN_TOKEN>`. When `ADMIN_TOKEN` is
//! unset the endpoint returns 503.
//!
//! Idempotent: re-running on the same catalog files just rebuilds the
//! same store. Safe to invoke from cron after a `lake exe extract` run.

use std::sync::Arc;

use axum::{
    Json,
    extract::State,
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
};
use nasrudin_derive::AxiomStore;

use crate::state::AppState;

/// `POST /api/admin/reload_corpus`
///
/// Response: `{ "count": N, "ast_count": M, "hot_swapped": true }`
/// where `count` is the total registered axioms and `ast_count` is the
/// subset whose `expr_ast` deserialised into a real `Expr` tree (vs.
/// the `Var(name)` placeholder fallback).
pub async fn reload_corpus(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
) -> impl IntoResponse {
    let expected = match &state.admin_token {
        Some(t) => t.clone(),
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({
                    "error": "admin_token_unset",
                    "hint": "set ADMIN_TOKEN in the API process environment"
                })),
            )
                .into_response();
        }
    };

    let provided = headers
        .get(axum::http::header::AUTHORIZATION)
        .and_then(|v| v.to_str().ok())
        .and_then(|s| s.strip_prefix("Bearer "))
        .unwrap_or("");
    if provided != expected {
        return (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "bad_admin_token" })),
        )
            .into_response();
    }

    // Rebuild the store using the same sequence as boot. Run the rebuild
    // on a blocking thread so the I/O (potentially several MB of JSON)
    // doesn't stall the tokio runtime.
    let prover_root = std::env::var("PROVER_ROOT").unwrap_or_else(|_| "../prover".into());
    let result = tokio::task::spawn_blocking(move || -> anyhow::Result<(AxiomStore, usize, usize)> {
        let mut store = AxiomStore::new();
        let catalog_path =
            std::path::Path::new(&prover_root).join("../physlean-extract/output/catalog.json");
        if catalog_path.exists() {
            store.load_from_catalog(&catalog_path)?;
        }
        store.load_special_relativity_upstream();
        store.load_electromagnetism_upstream();
        store.load_classical_mechanics_postulates();

        let math_corpus_path = std::path::Path::new(&prover_root)
            .join("../physlean-extract/output/math_corpus.json");
        let math_count = store.load_math_corpus(&math_corpus_path).unwrap_or(0);

        // Re-run the no-cheat audit. If the catalog has been tampered
        // with to register a forbidden headline, refuse to swap.
        nasrudin_derive::no_cheat_audit::audit_or_panic(&store, "reload_corpus");

        let total = store.len();
        Ok((store, total, math_count))
    })
    .await;

    let (new_store, total, math_count) = match result {
        Ok(Ok(triple)) => triple,
        Ok(Err(e)) => {
            tracing::error!("reload_corpus rebuild failed: {e}");
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("rebuild_failed: {e}") })),
            )
                .into_response();
        }
        Err(e) => {
            tracing::error!("reload_corpus join failed: {e}");
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("join_failed: {e}") })),
            )
                .into_response();
        }
    };

    state.axiom_store.replace(new_store);
    // Bust the seed-response cache so workers see the freshly-loaded
    // axioms on their next poll instead of waiting for TTL.
    if let Ok(mut map) = state.seed_cache.lock() {
        map.clear();
    }
    tracing::info!("Hot-reloaded AxiomStore: {total} axioms ({math_count} math-corpus entries)");

    (
        StatusCode::OK,
        Json(serde_json::json!({
            "count": total,
            "math_count": math_count,
            "hot_swapped": true
        })),
    )
        .into_response()
}

/// Bearer-token gate shared by every steerer admin endpoint. Returns
/// the gate's `Err` response (503 / 401) if the request fails the
/// check, else `Ok(())`.
fn check_admin(
    state: &AppState,
    headers: &HeaderMap,
) -> Result<(), (StatusCode, Json<serde_json::Value>)> {
    let expected = match &state.admin_token {
        Some(t) => t.clone(),
        None => {
            return Err((
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({ "error": "admin_token_unset" })),
            ));
        }
    };
    let provided = headers
        .get(axum::http::header::AUTHORIZATION)
        .and_then(|v| v.to_str().ok())
        .and_then(|s| s.strip_prefix("Bearer "))
        .unwrap_or("");
    if provided != expected {
        return Err((
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "bad_admin_token" })),
        ));
    }
    Ok(())
}

/// `GET /api/admin/steering/recent` — last 50 cluster-steerer cycles
/// (newest first). Lets ops eyeball mode flips, validation failures,
/// and the LLM's actual emitted configs over time.
pub async fn steering_recent(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
) -> impl IntoResponse {
    if let Err(e) = check_admin(&state, &headers) {
        return e.into_response();
    }
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response();
        }
    };
    match nasrudin_pg::query::cluster_steering::list_recent(pg, 50).await {
        Ok(rows) => (StatusCode::OK, Json(serde_json::json!({ "cycles": rows })))
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

/// `POST /api/admin/steering/force` — manual override. Body is a
/// `SteeringConfig`; persisted as a cycle row with model_id="admin"
/// + validation_failed=false (it's force-injected, validation already
/// performed). Hot-reloads the ArcSwap snapshot so workers see it
/// instantly.
pub async fn steering_force(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    Json(config): Json<crate::steerer::schema::SteeringConfig>,
) -> impl IntoResponse {
    if let Err(e) = check_admin(&state, &headers) {
        return e.into_response();
    }
    if let Err(e) = config.validate() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": format!("validation: {e}") })),
        )
            .into_response();
    }
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response();
        }
    };
    let value = serde_json::to_value(&config).unwrap_or(serde_json::Value::Null);
    let row = match nasrudin_pg::query::cluster_steering::insert_new_cycle(
        pg,
        &config.scope,
        value.clone(),
        "admin",
        false,
        None,
        None,
    )
    .await
    {
        Ok(r) => r,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
                .into_response();
        }
    };

    let body = serde_json::to_vec(&config).unwrap_or_default();
    let etag = xxhash_rust::xxh64::xxh64(&body, 0);
    state.steering.store(Arc::new(crate::state::SteeringSnapshot {
        config: value,
        etag,
        started_at: row.started_at.with_timezone(&chrono::Utc),
    }));
    state.invalidate_seed_cache();

    (
        StatusCode::OK,
        Json(serde_json::json!({ "cycle_id": row.id, "etag": format!("{etag:016x}") })),
    )
        .into_response()
}
