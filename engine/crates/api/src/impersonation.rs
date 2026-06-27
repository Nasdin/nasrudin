//! User impersonation: HMAC-signed tokens + axum middleware.
//!
//! Flow:
//! 1. Admin POSTs `/api/admin/users/{id}/impersonate` with a reason.
//!    Server inserts an `impersonation_sessions` row, mints an HMAC
//!    token over `(session_id, admin_user_id, target_user_id, expires_at)`,
//!    returns the token to the frontend.
//! 2. Frontend stores the token in `sessionStorage` and sends it via
//!    `X-Impersonate-Token` on every subsequent API call.
//! 3. `impersonation_layer` middleware validates the token, looks up
//!    the still-active session row, and injects `ImpersonationMarker`
//!    + a substitute `AuthUser` (the target's) into request extensions.
//! 4. The `AuthOrApiKey` extractor prefers the extension-injected
//!    AuthUser when present, so handlers transparently see the target.
//!
//! Sensitive endpoints (admin/*, billing/*, api_keys mint, login,
//! preferences write) are gated by `block_during_impersonation` which
//! rejects 403 when the marker is present.

use std::sync::Arc;

use axum::extract::{Request, State};
use axum::http::StatusCode;
use axum::middleware::Next;
use axum::response::{IntoResponse, Response};
use base64::Engine;
use chrono::{DateTime, Utc};
use hmac::{Hmac, KeyInit, Mac};
use serde::{Deserialize, Serialize};
use sha2::Sha256;
use uuid::Uuid;

use crate::auth::AuthUser;
use crate::state::AppState;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TokenPayload {
    pub session_id: Uuid,
    pub admin_user_id: Uuid,
    pub target_user_id: Uuid,
    pub expires_at: DateTime<Utc>,
}

#[derive(Debug, thiserror::Error)]
pub enum TokenError {
    #[error("malformed token")]
    Malformed,
    #[error("bad signature")]
    BadSignature,
    #[error("expired")]
    Expired,
}

/// Mint an HMAC-SHA256 token. Format is `<body_b64>.<sig_b64>` where
/// `body_b64` is `URL_SAFE_NO_PAD(json(payload))` and `sig_b64` is
/// `URL_SAFE_NO_PAD(hmac_sha256(secret, body_b64))`.
pub fn mint_token(secret: &[u8], payload: &TokenPayload) -> String {
    let body = serde_json::to_vec(payload).expect("TokenPayload is Serialize");
    let body_b64 = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(&body);
    let mut mac = Hmac::<Sha256>::new_from_slice(secret).expect("hmac key");
    mac.update(body_b64.as_bytes());
    let sig = mac.finalize().into_bytes();
    let sig_b64 = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(sig);
    format!("{body_b64}.{sig_b64}")
}

/// Verify a token's HMAC signature and unwrap its payload. Constant-time
/// signature compare via `hmac::Mac::verify_slice`.
pub fn verify_token(secret: &[u8], token: &str) -> Result<TokenPayload, TokenError> {
    let (body_b64, sig_b64) = token.split_once('.').ok_or(TokenError::Malformed)?;
    let mut mac = Hmac::<Sha256>::new_from_slice(secret).map_err(|_| TokenError::BadSignature)?;
    mac.update(body_b64.as_bytes());
    let provided = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(sig_b64)
        .map_err(|_| TokenError::BadSignature)?;
    mac.verify_slice(&provided)
        .map_err(|_| TokenError::BadSignature)?;
    let body = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(body_b64)
        .map_err(|_| TokenError::Malformed)?;
    let payload: TokenPayload = serde_json::from_slice(&body).map_err(|_| TokenError::Malformed)?;
    if payload.expires_at < Utc::now() {
        return Err(TokenError::Expired);
    }
    Ok(payload)
}

/// Marker placed in request extensions when an active impersonation
/// session is in flight. Carries the original admin id forward so the
/// audit log can record both the actor (target user) and the admin.
#[derive(Clone, Debug)]
pub struct ImpersonationMarker {
    pub session_id: Uuid,
    pub original_admin_id: Uuid,
}

/// Middleware. Looks for `X-Impersonate-Token`. On valid token + active
/// session row, injects:
/// - `ImpersonationMarker` for downstream handlers / audit code.
/// - `AuthUser` (target's) for `AuthOrApiKey` to pick up first.
pub async fn impersonation_layer(
    State(state): State<Arc<AppState>>,
    mut req: Request,
    next: Next,
) -> Response {
    let token = req
        .headers()
        .get("x-impersonate-token")
        .and_then(|v| v.to_str().ok())
        .map(str::to_string);
    let (Some(token), Some(secret)) = (token, state.impersonation_signing_key.as_deref()) else {
        return next.run(req).await;
    };
    let payload = match verify_token(secret, &token) {
        Ok(p) => p,
        Err(_) => return next.run(req).await,
    };
    let pg = match &state.pg {
        Some(p) => p,
        None => return next.run(req).await,
    };
    let active = nasrudin_pg::query::impersonation::find_active(pg, payload.session_id).await;
    let Ok(Some(_session)) = active else {
        return next.run(req).await;
    };
    if let Ok(Some(target_model)) =
        nasrudin_pg::query::users::find_by_id(pg, payload.target_user_id).await
    {
        let target = AuthUser::from_model(target_model);
        req.extensions_mut().insert(target);
        req.extensions_mut().insert(ImpersonationMarker {
            session_id: payload.session_id,
            original_admin_id: payload.admin_user_id,
        });
    }
    next.run(req).await
}

/// Guard layer: rejects with 403 `cannot_during_impersonation` if a
/// request carries an active `ImpersonationMarker`. Apply to admin,
/// auth, billing, api-key minting, and preferences-write routes.
pub async fn block_during_impersonation(req: Request, next: Next) -> Response {
    if req.extensions().get::<ImpersonationMarker>().is_some() {
        let body = serde_json::json!({"error": "cannot_during_impersonation"});
        return (StatusCode::FORBIDDEN, axum::Json(body)).into_response();
    }
    next.run(req).await
}
