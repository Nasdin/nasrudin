//! Worker registration + heartbeat + public list.
use axum::{Json, extract::{Query, State}, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

use crate::{auth::WorkerAuth, keygen, state::AppState};

/// 30-second TTL cache for `GET /api/workers`. The endpoint is public and
/// unauthenticated; the frontend polls it on a 30 s schedule + invalidates on
/// SSE heartbeat events anyway, so a 30 s server cache costs nothing visible
/// to users while collapsing concurrent traffic into a single PG round-trip.
const WORKERS_LIST_TTL: Duration = Duration::from_secs(30);

/// Pre-serialized JSON body cache. Single slot (no params on this endpoint).
/// `Arc<String>` so cache hits avoid both PG and re-serialisation.
#[derive(Default)]
pub struct WorkersListCache {
    inner: RwLock<Option<(Instant, Arc<String>)>>,
}

impl WorkersListCache {
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(None),
        }
    }

    async fn get_fresh(&self) -> Option<Arc<String>> {
        let g = self.inner.read().await;
        if let Some((ts, body)) = g.as_ref() {
            if ts.elapsed() < WORKERS_LIST_TTL {
                return Some(body.clone());
            }
        }
        None
    }

    async fn store(&self, body: Arc<String>) {
        *self.inner.write().await = Some((Instant::now(), body));
    }
}

#[derive(Deserialize)]
pub struct RegisterBody {
    pub handle: String,
    pub host: Option<String>,
}

#[derive(Deserialize)]
pub struct WorkersListQuery {
    pub limit: Option<u64>,
    pub cursor: Option<String>,
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

    // Check if this is a droplet worker (host contains "droplet" or similar indicator)
    // If so, attribute to the special user nasrudin.salim.suden@gmail.com
    let droplet_user_id = if let Some(host) = &body.host {
        if host.contains("droplet") {
            if let Ok(Some(user)) = nasrudin_pg::query::contributors::get_user_by_email(
                &db,
                "nasrudin.salim.suden@gmail.com",
            )
            .await
            {
                Some(user.id)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };

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
        droplet_user_id,
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
/// Supports pagination via `limit` and `cursor` query params. When
/// pagination params are provided, returns `{ workers, next_cursor }`.
/// When not provided, returns the full list (legacy behavior).
///
/// Returns `[]` (HTTP 200) when Postgres is unavailable so the frontend
/// leaderboard renders gracefully. 30 s in-process cache: the frontend
/// already revalidates every 30 s via React Query, so this is invisible
/// freshness-wise but collapses concurrent traffic into one PG round-trip.
pub async fn list(
    State(state): State<Arc<AppState>>,
    Query(query): Query<WorkersListQuery>,
) -> impl IntoResponse {
    // Only use cache for non-paginated requests (backward compatibility)
    if query.limit.is_none() && query.cursor.is_none() {
        if let Some(body) = state.workers_list_cache.get_fresh().await {
            return (
                StatusCode::OK,
                [(axum::http::header::CONTENT_TYPE, "application/json")],
                body.as_bytes().to_vec(),
            )
                .into_response();
        }
    }

    let Some(db) = state.pg.clone() else {
        let response = if query.limit.is_some() || query.cursor.is_some() {
            serde_json::json!({ "workers": [], "next_cursor": null })
        } else {
            serde_json::json!([])
        };
        return (StatusCode::OK, Json(response)).into_response();
    };

    let limit = query.limit.unwrap_or(50).min(100);
    // Snapshot the pagination shape *before* moving cursor into the query —
    // the legacy/paginated branch decision below needs the original input.
    let want_paginated = query.limit.is_some() || query.cursor.is_some();

    // Use paginated query if cursor or limit is provided
    let (rows, next_cursor) = match nasrudin_pg::query::workers::list_paginated(
        &db,
        limit,
        query.cursor,
    )
    .await
    {
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
                    "country_code": o.country_code,
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

    // Return paginated response if pagination params were provided
    if want_paginated {
        return (
            StatusCode::OK,
            Json(serde_json::json!({
                "workers": enriched,
                "next_cursor": next_cursor,
            })),
        )
            .into_response();
    }

    // Legacy response: return full list
    let body = serde_json::to_string(&enriched).unwrap_or_else(|_| "[]".to_string());
    let body_arc = Arc::new(body);
    state.workers_list_cache.store(body_arc.clone()).await;
    (
        StatusCode::OK,
        [(axum::http::header::CONTENT_TYPE, "application/json")],
        body_arc.as_bytes().to_vec(),
    )
        .into_response()
}
