//! Contributors/leaderboard endpoints — user-level aggregated stats.
use axum::{Json, extract::{Path, State}, http::StatusCode, response::IntoResponse};
use std::sync::Arc;
use std::time::Duration;

use crate::state::AppState;

/// 30-second TTL cache for `GET /api/contributors`.
const CONTRIBUTORS_LIST_TTL: Duration = Duration::from_secs(30);

#[derive(Default)]
pub struct ContributorsListCache {
    inner: tokio::sync::RwLock<Option<(std::time::Instant, Arc<String>)>>,
}

impl ContributorsListCache {
    pub fn new() -> Self {
        Self {
            inner: tokio::sync::RwLock::new(None),
        }
    }

    async fn get_fresh(&self) -> Option<Arc<String>> {
        let g = self.inner.read().await;
        if let Some((ts, body)) = g.as_ref() {
            if ts.elapsed() < CONTRIBUTORS_LIST_TTL {
                return Some(body.clone());
            }
        }
        None
    }

    async fn store(&self, body: Arc<String>) {
        *self.inner.write().await = Some((std::time::Instant::now(), body));
    }
}

/// `GET /api/contributors` — public list of users ranked by total theorems
/// contributed across all their workers.
pub async fn list(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    if let Some(body) = state.contributors_list_cache.get_fresh().await {
        return (
            StatusCode::OK,
            [(axum::http::header::CONTENT_TYPE, "application/json")],
            body.as_bytes().to_vec(),
        )
            .into_response();
    }

    let Some(db) = state.pg.clone() else {
        return (StatusCode::OK, Json(serde_json::json!([]))).into_response();
    };

    let contributors = match nasrudin_pg::query::contributors::list_contributors(&db).await {
        Ok(c) => c,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            )
                .into_response();
        }
    };

    let body = serde_json::to_string(&contributors).unwrap_or_else(|_| "[]".to_string());
    let body_arc = Arc::new(body);
    state.contributors_list_cache.store(body_arc.clone()).await;
    (
        StatusCode::OK,
        [(axum::http::header::CONTENT_TYPE, "application/json")],
        body_arc.as_bytes().to_vec(),
    )
        .into_response()
}

/// `GET /api/contributors/:id` — get a specific user's workers.
pub async fn get_user_workers(
    State(state): State<Arc<AppState>>,
    Path(user_id): Path<String>,
) -> axum::response::Response {
    let Some(db) = state.pg.clone() else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "postgres not configured" })),
        )
            .into_response();
    };

    let uuid = match uuid::Uuid::parse_str(&user_id) {
        Ok(u) => u,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": "invalid user id" })),
            )
                .into_response();
        }
    };

    let workers = match nasrudin_pg::query::contributors::get_user_workers(&db, uuid).await {
        Ok(w) => w,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            )
                .into_response();
        }
    };

    // Enrich with owner info (same pattern as workers list)
    let owners = nasrudin_pg::query::me_workers::owner_map(&db)
        .await
        .unwrap_or_default();

    let enriched: Vec<serde_json::Value> = workers
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

    (StatusCode::OK, Json(enriched)).into_response()
}
