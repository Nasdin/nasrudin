//! User API key management — cookie-session-only handlers.
use axum::{Json, extract::Path, http::StatusCode, response::IntoResponse};
use serde::Deserialize;
use uuid::Uuid;

use crate::{auth::AuthSess, keygen};

#[derive(Deserialize)]
pub struct CreateBody {
    pub name: String,
    pub expires_in_days: Option<i64>,
    /// `"live"` (default) for read/server-to-server keys, `"worker"` for
    /// distributed-discovery binaries that POST to `/api/ingest`. A `worker`
    /// key also registers a row in the `workers` table keyed on `name`.
    #[serde(default)]
    pub kind: Option<String>,
}

/// `POST /api/api-keys` — cookie auth only.
pub async fn create(auth: AuthSess, Json(body): Json<CreateBody>) -> impl IntoResponse {
    let Some(user) = auth.user.as_ref() else {
        return (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "not authenticated" })),
        );
    };

    let name = body.name.trim();
    if name.is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({ "error": "name is required" })),
        );
    }

    let kind = match body.kind.as_deref().unwrap_or("live") {
        "live" => "live",
        "worker" => "worker",
        other => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": format!("unknown kind '{other}'") })),
            );
        }
    };

    let generated = match keygen::generate(kind) {
        Ok(k) => k,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("{e}") })),
            );
        }
    };

    if kind == "worker"
        && let Err(e) =
            nasrudin_pg::query::workers::register(&auth.backend.db, name, Some(name), None).await
        && !format!("{e}").contains("duplicate key")
    {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("worker_register: {e}") })),
        );
    }

    let expires_at = body
        .expires_in_days
        .map(|d| chrono::Utc::now() + chrono::Duration::days(d));

    let row = match nasrudin_pg::query::api_keys::create(
        &auth.backend.db,
        Some(user.id),
        kind,
        name,
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
            "kind": row.kind,
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
                        "kind": r.kind,
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
