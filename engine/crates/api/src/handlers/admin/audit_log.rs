//! `GET /api/admin/audit` — filtered audit-log listing.

use std::sync::Arc;

use axum::{
    Json,
    extract::{Query, State},
    http::StatusCode,
    response::IntoResponse,
};
use serde::Deserialize;
use serde_json::json;
use uuid::Uuid;

use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct ListQ {
    pub actor_user_id: Option<Uuid>,
    pub target_user_id: Option<Uuid>,
    pub action: Option<String>,
    #[serde(default = "default_limit")]
    pub limit: u64,
    #[serde(default)]
    pub offset: u64,
}

fn default_limit() -> u64 {
    100
}

pub async fn list(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Query(q): Query<ListQ>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(json!({"error": "pg_unavailable"})),
            )
                .into_response();
        }
    };
    match nasrudin_pg::query::admin_audit_log::list_filtered(
        pg,
        q.actor_user_id,
        q.target_user_id,
        q.action.as_deref(),
        q.limit.min(500),
        q.offset,
    )
    .await
    {
        Ok(rows) => (StatusCode::OK, Json(json!({"entries": rows}))).into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": e.to_string()})),
        )
            .into_response(),
    }
}
