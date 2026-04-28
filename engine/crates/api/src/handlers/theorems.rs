//! `GET /api/theorems`, `…/recent`, `…/{id}`, `…/{hash}/lean`.
//!
//! Phase 9 / Task 5.1. All four read endpoints serve directly out of the
//! PostgreSQL `theorems` mirror (see `nasrudin_pg::query::theorems`) so the
//! frontend always sees the canonical "verified + persisted" view rather than
//! the in-flight RocksDB row, which can include `Pending` and `Rejected`
//! statuses.
//!
//! When PostgreSQL is not configured the daemon still boots, but every
//! endpoint here returns `503 Service Unavailable` with `error =
//! "pg_unavailable"` — making it a soft failure mode that the frontend can
//! detect and degrade gracefully.

use axum::{
    Json,
    extract::{Path, Query, State},
    http::{StatusCode, header},
    response::IntoResponse,
};
use serde::Deserialize;
use std::sync::Arc;

use crate::state::AppState;
use nasrudin_pg::query::theorems;

/// Query params shared by `list` and `recent`. `recent` ignores `cursor`.
#[derive(Deserialize)]
pub struct ListQuery {
    pub limit: Option<u64>,
    pub cursor: Option<String>,
    pub domain: Option<String>,
}

/// `GET /api/theorems` — cursor-paginated `Verified` list, newest-first.
///
/// Returns `{ theorems, next_cursor, total, total_capped }`. `total` is
/// COUNT(*) capped at 10 000; when the true count exceeds that, `total_capped`
/// is `true` so the UI can render "10,000+" without lying.
pub async fn list(
    State(state): State<Arc<AppState>>,
    Query(q): Query<ListQuery>,
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
    let limit = q.limit.unwrap_or(50).min(500);
    match theorems::list_verified(pg, q.cursor, limit, q.domain).await {
        Ok(page) => (
            StatusCode::OK,
            Json(serde_json::json!({
                "theorems": page.items,
                "next_cursor": page.next_cursor,
                "total": page.total,
                "total_capped": page.total_capped,
            })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

/// `GET /api/theorems/recent` — same query shape as `list` but the cursor
/// param is dropped before the DB call so it always returns the newest page.
pub async fn recent(
    State(state): State<Arc<AppState>>,
    Query(mut q): Query<ListQuery>,
) -> impl IntoResponse {
    q.cursor = None;
    list(State(state), Query(q)).await
}

/// `GET /api/theorems/{id}` — fetch one theorem by its 8-byte hex id.
///
/// `id` must be 16 hex chars. Anything malformed → 400; not found → 404.
pub async fn by_id(
    State(state): State<Arc<AppState>>,
    Path(id): Path<String>,
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
    let id_bytes = match hex::decode(&id) {
        Ok(b) => b,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": "bad_id" })),
            )
                .into_response();
        }
    };
    match theorems::get_by_id(pg, &id_bytes).await {
        Ok(Some(t)) => (StatusCode::OK, Json(t)).into_response(),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not_found" })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}

/// `GET /api/theorems/{hash}/lean` — download the Lean source for a verified
/// theorem as `text/plain` with a `Content-Disposition: attachment` filename.
///
/// `hash` is the 8-byte canonical hash hex-encoded — the same identity the
/// frontend uses to dedupe rows, distinct from the primary-key `id` used by
/// `by_id` even though in Phase 9 they happen to be the same value.
pub async fn lean_download(
    State(state): State<Arc<AppState>>,
    Path(hash): Path<String>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => return (StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable").into_response(),
    };
    let hash_bytes = match hex::decode(&hash) {
        Ok(b) => b,
        Err(_) => return (StatusCode::BAD_REQUEST, "bad_hash").into_response(),
    };
    match theorems::get_by_canonical_hash(pg, &hash_bytes).await {
        Ok(Some(t)) => {
            let filename = format!("theorem_{}.lean", hex::encode(&t.canonical_hash));
            let cd = format!("attachment; filename=\"{filename}\"");
            (
                StatusCode::OK,
                [
                    (header::CONTENT_TYPE, "text/plain; charset=utf-8".to_string()),
                    (header::CONTENT_DISPOSITION, cd),
                ],
                t.lean_source,
            )
                .into_response()
        }
        Ok(None) => (StatusCode::NOT_FOUND, "not_found").into_response(),
        Err(_) => (StatusCode::INTERNAL_SERVER_ERROR, "db_error").into_response(),
    }
}
