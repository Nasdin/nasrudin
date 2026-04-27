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

#[derive(Deserialize)]
pub struct HeartbeatBody {
    pub theorems_contributed: i64,
}

pub async fn heartbeat(
    State(state): State<Arc<AppState>>,
    auth: WorkerAuth,
    Json(body): Json<HeartbeatBody>,
) -> impl IntoResponse {
    let Some(db) = state.pg.clone() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "postgres not configured" })),
        );
    };
    match nasrudin_pg::query::workers::heartbeat(
        &db,
        &auth.0.worker_handle,
        body.theorems_contributed,
    )
    .await
    {
        Ok(Some(row)) => (StatusCode::OK, Json(serde_json::to_value(row).unwrap())),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "worker not found" })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

/// `GET /api/workers` — public list of all known workers.
pub async fn list(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let Some(db) = state.pg.clone() else {
        return (StatusCode::OK, Json(serde_json::json!({ "workers": [] })));
    };
    match nasrudin_pg::query::workers::list(&db, None).await {
        Ok(rows) => (StatusCode::OK, Json(serde_json::json!({ "workers": rows }))),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}
