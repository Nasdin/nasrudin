//! User preferences — JSON merge. Accepts cookie or Bearer.
use axum::{Json, http::StatusCode, response::IntoResponse};

use crate::auth::{AuthOrApiKey, AuthSess};

pub async fn get(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    match nasrudin_pg::query::user_preferences::get(&auth_sess.backend.db, auth.user.id).await {
        Ok(prefs) => (
            StatusCode::OK,
            Json(serde_json::json!({ "preferences": prefs })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

pub async fn patch(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    if !body.is_object() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "body must be a JSON object" })),
        );
    }
    match nasrudin_pg::query::user_preferences::merge(&auth_sess.backend.db, auth.user.id, body)
        .await
    {
        Ok(row) => (
            StatusCode::OK,
            Json(serde_json::json!({ "preferences": row.preferences })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}
