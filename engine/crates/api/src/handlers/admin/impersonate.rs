//! `POST /api/admin/users/{id}/impersonate` and
//! `POST /api/admin/impersonate/end`.
//!
//! Start: validates `target ≠ self` and `target.is_admin = false`,
//! inserts an `impersonation_sessions` row, mints an HMAC token, and
//! returns it. The frontend stores the token in `sessionStorage` and
//! sends it via `X-Impersonate-Token` on subsequent calls.
//!
//! End: marks the session ended manually. Idempotent — calling on an
//! already-ended session returns 200.

use std::net::SocketAddr;
use std::sync::Arc;

use axum::{
    Json,
    extract::{ConnectInfo, Path, State},
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
};
use serde::Deserialize;
use serde_json::json;
use uuid::Uuid;

use crate::admin::audit::{RequestMeta, actions, perform_audited};
use crate::admin::require_admin::RequireAdmin;
use crate::impersonation::{TokenPayload, mint_token};
use crate::state::AppState;

#[derive(Deserialize)]
pub struct StartInput {
    /// Clamp [60, 3600] seconds. Default 900 (15 min).
    #[serde(default = "default_duration")]
    pub duration_seconds: i64,
    pub reason: String,
}

fn default_duration() -> i64 {
    900
}

pub async fn start(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(target_id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<StartInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let key = match state.impersonation_signing_key.as_deref() {
        Some(k) => k,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(json!({"error": "signing_key_unset"})),
            )
                .into_response();
        }
    };
    if target_id == admin.0.user.id {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "cannot_impersonate_self"})),
        )
            .into_response();
    }
    let target = match nasrudin_pg::query::admin_users::find_by_id(pg, target_id).await {
        Ok(Some(u)) => u,
        Ok(None) => {
            return (StatusCode::NOT_FOUND, Json(json!({"error": "not_found"}))).into_response();
        }
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({"error": e.to_string()})),
            )
                .into_response();
        }
    };
    if target.is_admin {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "cannot_impersonate_admin"})),
        )
            .into_response();
    }
    let duration = body.duration_seconds.clamp(60, 3600);
    let expires_at = chrono::Utc::now() + chrono::Duration::seconds(duration);
    let admin_id = admin.0.user.id;
    let req_meta = RequestMeta {
        ip: Some(addr.ip()),
        user_agent: headers
            .get(axum::http::header::USER_AGENT)
            .and_then(|v| v.to_str().ok())
            .map(str::to_string),
    };
    let reason = body.reason.clone();

    let row_result: Result<nasrudin_pg::entity::impersonation_sessions::Model, _> =
        perform_audited(
            pg,
            &admin.0.user,
            None,
            req_meta,
            Some(target_id),
            actions::IMPERSONATE_START,
            body.reason,
            json!({"target_user_id": target_id, "duration_seconds": duration}),
            move |txn| {
                Box::pin(async move {
                    let row = nasrudin_pg::query::impersonation::start(
                        txn, admin_id, target_id, expires_at, reason,
                    )
                    .await?;
                    let row_id = row.id;
                    Ok::<_, sea_orm::DbErr>((
                        row,
                        json!({"session_id": row_id, "expires_at": expires_at}),
                    ))
                })
            },
        )
        .await;
    let session_row = match row_result {
        Ok(r) => r,
        Err(crate::admin::audit::AuditError::ReasonTooShort) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "reason_too_short"})),
            )
                .into_response();
        }
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(json!({"error": e.to_string()})),
            )
                .into_response();
        }
    };
    let payload = TokenPayload {
        session_id: session_row.id,
        admin_user_id: admin_id,
        target_user_id: target_id,
        expires_at,
    };
    let token = mint_token(key, &payload);
    (
        StatusCode::OK,
        Json(json!({
            "token": token,
            "session_id": session_row.id,
            "target_email": target.email,
            "expires_at": expires_at,
        })),
    )
        .into_response()
}

#[derive(Deserialize)]
pub struct EndInput {
    pub session_id: Uuid,
}

pub async fn end_impersonation(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<EndInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let req_meta = RequestMeta {
        ip: Some(addr.ip()),
        user_agent: headers
            .get(axum::http::header::USER_AGENT)
            .and_then(|v| v.to_str().ok())
            .map(str::to_string),
    };
    let session_id = body.session_id;
    let result: Result<(), _> = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta,
        None,
        actions::IMPERSONATE_END,
        "ended by admin (manual)".into(),
        json!({"session_id": session_id}),
        move |txn| {
            Box::pin(async move {
                // end() is idempotent for our purposes: if the session
                // is already ended, the SQL UPDATE just touches no rows.
                nasrudin_pg::query::impersonation::end(txn, session_id, "manual")
                    .await
                    .ok();
                Ok::<_, sea_orm::DbErr>(((), json!({"ended": true})))
            })
        },
    )
    .await;
    match result {
        Ok(()) => (StatusCode::OK, Json(json!({"ok": true}))).into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": e.to_string()})),
        )
            .into_response(),
    }
}
