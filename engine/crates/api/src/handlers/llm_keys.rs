//! BYO LLM key vault: `GET`/`POST`/`DELETE` `/api/me/llm-keys`.

use axum::{
    Json,
    extract::{Path, State},
    http::StatusCode,
    response::{IntoResponse, Response},
};
use nasrudin_llm::{Registry, encryption};
use nasrudin_pg::query::user_llm_keys as keys_q;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::auth::{AuthOrApiKey, AuthSess};
use crate::state::AppState;

#[derive(Serialize)]
pub struct KeySummaryDto {
    pub provider: String,
    pub key_hint: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub last_used_at: Option<chrono::DateTime<chrono::Utc>>,
}

#[derive(Deserialize)]
pub struct SetKeyBody {
    pub provider: String,
    pub key: String,
}

#[derive(Serialize)]
pub struct ListResponse {
    pub keys: Vec<KeySummaryDto>,
    pub known_providers: Vec<&'static str>,
}

pub async fn list(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
) -> Response {
    if state.llm_encrypt_key.is_none() {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({"error": "key_encrypt_unset"})),
        )
            .into_response();
    }
    let db = &auth_sess.backend.db;
    match keys_q::list_for_user(db, auth.user.id).await {
        Ok(rows) => {
            let dto: Vec<KeySummaryDto> = rows
                .into_iter()
                .map(|s| KeySummaryDto {
                    provider: s.provider,
                    key_hint: s.key_hint,
                    created_at: s.created_at,
                    last_used_at: s.last_used_at,
                })
                .collect();
            Json(ListResponse {
                keys: dto,
                known_providers: Registry::known_providers().to_vec(),
            })
            .into_response()
        }
        Err(e) => {
            tracing::warn!("list llm keys failed: {e}");
            (StatusCode::INTERNAL_SERVER_ERROR, "db error").into_response()
        }
    }
}

pub async fn set_key(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<SetKeyBody>,
) -> Response {
    let key_bytes = match state.llm_encrypt_key.as_ref() {
        Some(k) => k,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({"error": "key_encrypt_unset"})),
            )
                .into_response();
        }
    };
    if !Registry::known_providers().contains(&body.provider.as_str()) {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({
                "error": "unknown_provider",
                "known": Registry::known_providers()
            })),
        )
            .into_response();
    }
    if body.key.trim().is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(serde_json::json!({"error": "empty_key"})),
        )
            .into_response();
    }
    let encrypted = match encryption::encrypt(&body.key, key_bytes) {
        Ok(e) => e,
        Err(e) => {
            tracing::warn!("encrypt failed: {e}");
            return (StatusCode::INTERNAL_SERVER_ERROR, "encrypt failed").into_response();
        }
    };
    let hint = encryption::key_hint(&body.key);
    let db = &auth_sess.backend.db;
    if let Err(e) = keys_q::upsert(
        db,
        auth.user.id,
        body.provider.clone(),
        encrypted.0,
        hint.clone(),
    )
    .await
    {
        tracing::warn!("upsert llm key failed: {e}");
        return (StatusCode::INTERNAL_SERVER_ERROR, "db error").into_response();
    }
    Json(serde_json::json!({
        "provider": body.provider,
        "key_hint": hint,
    }))
    .into_response()
}

pub async fn revoke(
    State(_state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Path(provider): Path<String>,
) -> Response {
    let db = &auth_sess.backend.db;
    match keys_q::delete(db, auth.user.id, &provider).await {
        Ok(0) => (StatusCode::NOT_FOUND, "no such key").into_response(),
        Ok(_) => (StatusCode::NO_CONTENT, "").into_response(),
        Err(e) => {
            tracing::warn!("delete llm key failed: {e}");
            (StatusCode::INTERNAL_SERVER_ERROR, "db error").into_response()
        }
    }
}
