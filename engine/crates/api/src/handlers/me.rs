//! Per-user stat aggregation.
use axum::{Json, http::StatusCode, response::IntoResponse};

use crate::auth::{AuthOrApiKey, AuthSess};

/// `GET /api/me/stats`
pub async fn stats(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    let saved_count =
        nasrudin_pg::query::saved_searches::list_by_user(&auth_sess.backend.db, auth.user.id)
            .await
            .map(|v| v.len())
            .unwrap_or(0);
    let key_count = nasrudin_pg::query::api_keys::list_by_user(&auth_sess.backend.db, auth.user.id)
        .await
        .map(|v| v.len())
        .unwrap_or(0);
    (
        StatusCode::OK,
        Json(serde_json::json!({
            "saved_searches": saved_count,
            "api_keys": key_count,
        })),
    )
}
