//! Read-only access to the corpus embedding index.

use std::sync::Arc;

use axum::{
    Json,
    body::Body,
    extract::State,
    http::{StatusCode, header},
    response::{IntoResponse, Response},
};
use serde::Serialize;
use tokio_util::io::ReaderStream;

use crate::state::AppState;

#[derive(Serialize)]
pub struct ChecksumResponse {
    pub hex: String,
    pub bytes: u64,
    pub built_at_millis: i64,
    pub count: u32,
}

/// `GET /api/embed/checksum` — cheap call workers make every heartbeat.
pub async fn checksum(State(state): State<Arc<AppState>>) -> Response {
    let path = match &state.embed_path {
        Some(p) => p.clone(),
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({"error": "embed_disabled"})),
            )
                .into_response();
        }
    };
    let cs = match nasrudin_embed::compute_index_checksum(&path) {
        Ok(c) => c,
        Err(e) => {
            tracing::warn!("checksum compute failed: {e}");
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({
                    "error": "checksum_failed",
                    "detail": e.to_string()
                })),
            )
                .into_response();
        }
    };
    let header = state
        .embed
        .as_ref()
        .map(|i| i.header())
        .unwrap_or(nasrudin_embed::IndexHeader {
            version: nasrudin_embed::INDEX_VERSION,
            dim: nasrudin_embed::EMBED_DIM,
            count: 0,
            built_at_millis: 0,
        });
    Json(ChecksumResponse {
        hex: cs.hex,
        bytes: cs.bytes,
        built_at_millis: header.built_at_millis,
        count: header.count,
    })
    .into_response()
}

/// `GET /api/embed/index.bin` — streams the raw `corpus.embed` body.
/// The HNSW sidecar is rebuilt locally by the worker on download
/// (faster than streaming a serialised HNSW which is much larger).
pub async fn index_bin(State(state): State<Arc<AppState>>) -> Response {
    let path = match &state.embed_path {
        Some(p) => p.clone(),
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({"error": "embed_disabled"})),
            )
                .into_response();
        }
    };
    let file = match tokio::fs::File::open(&path).await {
        Ok(f) => f,
        Err(e) => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({
                    "error": "index_missing",
                    "detail": e.to_string()
                })),
            )
                .into_response();
        }
    };
    let stream = ReaderStream::new(file);
    let body = Body::from_stream(stream);
    let cs = nasrudin_embed::compute_index_checksum(&path).ok();
    let mut resp = Response::builder().header(header::CONTENT_TYPE, "application/octet-stream");
    if let Some(c) = &cs {
        resp = resp.header("Sha-Embed", c.hex.as_str());
    }
    resp.body(body)
        .unwrap_or_else(|_| (StatusCode::INTERNAL_SERVER_ERROR, Body::empty()).into_response())
}
