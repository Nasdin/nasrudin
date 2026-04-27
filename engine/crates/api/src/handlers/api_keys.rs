//! User API key management — cookie-session-only handlers.
use axum::{Json, extract::Path, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use uuid::Uuid;

use crate::{auth::AuthSess, keygen};

#[derive(Deserialize)]
pub struct CreateBody {
    pub name: String,
    pub expires_in_days: Option<i64>,
}

/// `POST /api/api-keys` — cookie auth only.
pub async fn create(auth: AuthSess, Json(body): Json<CreateBody>) -> impl IntoResponse {
    let Some(user) = auth.user.as_ref() else {
        return (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "not authenticated" })),
        );
    };

    if body.name.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "name is required" })),
        );
    }

    let generated = match keygen::generate("live") {
        Ok(k) => k,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            );
        }
    };

    let expires_at = body
        .expires_in_days
        .map(|d| chrono::Utc::now() + chrono::Duration::days(d));

    let row = match nasrudin_pg::query::api_keys::create(
        &auth.backend.db,
        Some(user.id),
        "live",
        body.name.trim(),
        &generated.prefix,
        &generated.hash,
        expires_at,
    )
    .await
    {
        Ok(r) => r,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            );
        }
    };

    (
        StatusCode::OK,
        Json(serde_json::json!({
            "id": row.id,
            "name": row.name,
            "prefix": row.prefix,
            "full_key": generated.full,
            "created_at": row.created_at,
            "expires_at": row.expires_at,
        })),
    )
}

/// `GET /api/api-keys`
pub async fn list(auth: AuthSess) -> impl IntoResponse {
    let Some(user) = auth.user.as_ref() else {
        return (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "not authenticated" })),
        );
    };
    match nasrudin_pg::query::api_keys::list_by_user(&auth.backend.db, user.id).await {
        Ok(rows) => {
            let keys: Vec<serde_json::Value> = rows
                .into_iter()
                .map(|r| {
                    serde_json::json!({
                        "id": r.id,
                        "name": r.name,
                        "prefix": r.prefix,
                        "last_used_at": r.last_used_at,
                        "created_at": r.created_at,
                        "expires_at": r.expires_at,
                    })
                })
                .collect();
            (StatusCode::OK, Json(serde_json::json!({ "keys": keys })))
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

/// `DELETE /api/api-keys/{id}`
pub async fn revoke(auth: AuthSess, Path(id): Path<Uuid>) -> impl IntoResponse {
    let Some(user) = auth.user.as_ref() else {
        return (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "not authenticated" })),
        );
    };
    match nasrudin_pg::query::api_keys::revoke(&auth.backend.db, id, user.id).await {
        Ok(Some(_)) => (StatusCode::OK, Json(serde_json::json!({ "revoked": true }))),
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
