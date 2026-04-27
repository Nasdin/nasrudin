//! Saved searches — accepts cookie session OR Bearer nsk_live_ keys.
use axum::{Json, extract::Path, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use uuid::Uuid;

use crate::auth::{AuthOrApiKey, AuthSess};

#[derive(Deserialize)]
pub struct CreateBody {
    pub latex: String,
    pub label: Option<String>,
}

#[derive(Deserialize)]
pub struct PatchBody {
    pub label: Option<String>,
}

pub async fn create(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<CreateBody>,
) -> impl IntoResponse {
    if body.latex.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "latex is required" })),
        );
    }
    match nasrudin_pg::query::saved_searches::create(
        &auth_sess.backend.db,
        auth.user.id,
        body.latex.trim(),
        body.label.as_deref(),
    )
    .await
    {
        Ok(row) => (StatusCode::OK, Json(serde_json::to_value(row).unwrap())),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

pub async fn list(auth: AuthOrApiKey, auth_sess: AuthSess) -> impl IntoResponse {
    match nasrudin_pg::query::saved_searches::list_by_user(&auth_sess.backend.db, auth.user.id)
        .await
    {
        Ok(rows) => (
            StatusCode::OK,
            Json(serde_json::json!({ "saved_searches": rows })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

pub async fn delete(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
) -> impl IntoResponse {
    match nasrudin_pg::query::saved_searches::delete(&auth_sess.backend.db, id, auth.user.id).await
    {
        Ok(res) if res.rows_affected > 0 => {
            (StatusCode::OK, Json(serde_json::json!({ "deleted": true })))
        }
        Ok(_) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not found" })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

pub async fn patch_label(
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(id): Path<Uuid>,
    Json(body): Json<PatchBody>,
) -> impl IntoResponse {
    match nasrudin_pg::query::saved_searches::update_label(
        &auth_sess.backend.db,
        id,
        auth.user.id,
        body.label.as_deref(),
    )
    .await
    {
        Ok(Some(row)) => (StatusCode::OK, Json(serde_json::to_value(row).unwrap())),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not found" })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}
