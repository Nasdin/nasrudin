//! Worker registration + heartbeat + public list.
use axum::{Json, extract::State, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use std::sync::Arc;

use crate::{auth::WorkerAuth, keygen, state::AppState};

#[derive(Deserialize)]
pub struct RegisterBody {
    pub handle: String,
    pub host: Option<String>,
}

/// `POST /api/workers/register` — unauthenticated. Returns `{ worker_id, api_key }`.
pub async fn register(
    State(state): State<Arc<AppState>>,
    Json(body): Json<RegisterBody>,
) -> impl IntoResponse {
    let Some(db) = state.pg.clone() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "postgres not configured" })),
        );
    };

    if body.handle.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "handle is required" })),
        );
    }

    if let Err(e) = nasrudin_pg::query::workers::register(
        &db,
        body.handle.trim(),
        Some(body.handle.trim()),
        body.host.as_deref(),
    )
    .await
    {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        );
    }

    let generated = match keygen::generate("worker") {
        Ok(k) => k,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            );
        }
    };
    if let Err(e) = nasrudin_pg::query::api_keys::create(
        &db,
        None,
        "worker",
        body.handle.trim(),
        &generated.prefix,
        &generated.hash,
        None,
    )
    .await
    {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        );
    }

    (
        StatusCode::OK,
        Json(serde_json::json!({
            "worker_id": body.handle.trim(),
            "api_key": generated.full,
        })),
    )
}

/// `POST /api/workers/heartbeat` body shape (Phase 9 Task 6.1).
#[derive(Deserialize)]
pub struct HeartbeatBody {
    pub worker_id: String,
    pub current_generation: i64,
    pub theorems_produced_total: i64,
    pub uptime_seconds: i64,
    pub engine_git_sha: String,
}

/// `POST /api/workers/heartbeat` — `WorkerAuth` (Bearer `nsk_worker_…`).
///
/// Body's `worker_id` must match the credential's worker handle, otherwise
/// `403`. Updates `last_heartbeat_at`, generation stats, uptime, and git SHA.
pub async fn heartbeat(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Json(body): Json<HeartbeatBody>,
) -> impl IntoResponse {
    if auth.0.worker_handle != body.worker_id {
        return (
            StatusCode::FORBIDDEN,
            Json(serde_json::json!({ "error": "id_mismatch" })),
        )
            .into_response();
    }
    let Some(db) = state.pg.clone() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "pg_unavailable" })),
        )
            .into_response();
    };
    match nasrudin_pg::query::workers::update_heartbeat(
        &db,
        &body.worker_id,
        body.current_generation,
        body.theorems_produced_total,
        body.uptime_seconds,
        &body.engine_git_sha,
    )
    .await
    {
        Ok(()) => (StatusCode::OK, Json(serde_json::json!({ "ok": true }))).into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        )
            .into_response(),
    }
}

/// `GET /api/workers` — public list of all known workers, ordered by
/// `theorems_contributed DESC`. Each row is enriched with `owner` info
/// (display name and email-local handle) when the worker's api-key is
/// linked to a user account; otherwise `owner` is `null` (anonymous worker
/// registered via `POST /api/workers/register`).
///
/// Returns `[]` (HTTP 200) when Postgres is unavailable so the frontend
/// leaderboard renders gracefully.
pub async fn list(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let Some(db) = state.pg.clone() else {
        return (StatusCode::OK, Json(serde_json::json!([]))).into_response();
    };
    let rows = match nasrudin_pg::query::workers::list_all(&db).await {
        Ok(r) => r,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            )
                .into_response();
        }
    };
    let owners = nasrudin_pg::query::me_workers::owner_map(&db)
        .await
        .unwrap_or_default();

    let enriched: Vec<serde_json::Value> = rows
        .into_iter()
        .map(|w| {
            let owner = owners.get(&w.id).map(|o| {
                serde_json::json!({
                    "user_id": o.user_id,
                    "display_name": o.display_name,
                    "handle": o.email_local,
                })
            });
            serde_json::json!({
                "id": w.id,
                "name": w.name,
                "host": w.host,
                "last_seen": w.last_seen,
                "theorems_contributed": w.theorems_contributed,
                "status": w.status,
                "last_heartbeat_at": w.last_heartbeat_at,
                "last_contribution_at": w.last_contribution_at,
                "current_generation": w.current_generation,
                "theorems_produced_total": w.theorems_produced_total,
                "uptime_seconds": w.uptime_seconds,
                "engine_git_sha": w.engine_git_sha,
                "owner": owner,
            })
        })
        .collect();
    (StatusCode::OK, Json(serde_json::json!(enriched))).into_response()
}
