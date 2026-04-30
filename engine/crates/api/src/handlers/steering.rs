//! `GET /api/steering` — current LLM cluster-steering snapshot.
//!
//! Reads `state.steering` (an `ArcSwap<SteeringSnapshot>`) and returns
//! the live config plus an ETag-encoded version. Workers fetch this
//! either directly (separate from `/api/seed`) or via the `steering`
//! field folded into the seed payload — both paths see the same
//! ArcSwap-backed snapshot.
//!
//! Conditional GET via `If-None-Match` returns 304 with no body. The
//! ETag is `xxhash64(serialised_config)` formatted as 16 hex chars.

use std::sync::Arc;

use axum::{
    extract::State,
    http::{header, HeaderMap, StatusCode},
    response::IntoResponse,
    Json,
};

use crate::state::AppState;

pub async fn steering(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
) -> impl IntoResponse {
    let snap = state.steering.load();
    let etag = format!("\"{:016x}\"", snap.etag);
    if let Some(c) = headers
        .get(header::IF_NONE_MATCH)
        .and_then(|v| v.to_str().ok())
    {
        if c == etag {
            return (
                StatusCode::NOT_MODIFIED,
                [
                    (header::ETAG, etag.clone()),
                    (
                        header::CACHE_CONTROL,
                        "public, max-age=30, stale-while-revalidate=300".to_string(),
                    ),
                ],
            )
                .into_response();
        }
    }
    let scope = snap
        .config
        .get("scope")
        .and_then(|v| v.as_str())
        .unwrap_or("?")
        .to_owned();
    (
        StatusCode::OK,
        [
            (header::CONTENT_TYPE, "application/json".to_string()),
            (header::ETAG, etag),
            (
                header::CACHE_CONTROL,
                "public, max-age=30, stale-while-revalidate=300".to_string(),
            ),
        ],
        Json(serde_json::json!({
            "config": snap.config,
            "mode": scope,
            "started_at": snap.started_at.to_rfc3339(),
        })),
    )
        .into_response()
}
