//! API-key admin handlers: revoke + per-key trust override.

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
use crate::state::AppState;
use crate::trust::CacheInvalidation;

fn req_meta(headers: &HeaderMap, addr: SocketAddr) -> RequestMeta {
    RequestMeta {
        ip: Some(addr.ip()),
        user_agent: headers
            .get(axum::http::header::USER_AGENT)
            .and_then(|v| v.to_str().ok())
            .map(str::to_string),
    }
}

#[derive(Deserialize)]
pub struct RevokeInput {
    pub reason: String,
}

pub async fn revoke(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<RevokeInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    use sea_orm::EntityTrait;
    let row = match nasrudin_pg::entity::api_keys::Entity::find_by_id(id)
        .one(pg)
        .await
    {
        Ok(Some(r)) => r,
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
    let target_user_id = row.user_id;
    let before_revoked = row.revoked_at.is_some();
    let key_name = row.name.clone();
    let result = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta(&headers, addr),
        target_user_id,
        actions::REVOKE_API_KEY,
        body.reason,
        json!({"name": key_name, "previously_revoked": before_revoked}),
        move |txn| {
            Box::pin(async move {
                sea_orm::ConnectionTrait::execute_raw(
                    txn,
                    sea_orm::Statement::from_sql_and_values(
                        sea_orm::DatabaseBackend::Postgres,
                        "UPDATE api_keys SET revoked_at=now() WHERE id=$1",
                        [id.into()],
                    ),
                )
                .await?;
                Ok::<_, sea_orm::DbErr>(((), json!({"revoked": true})))
            })
        },
    )
    .await;
    if result.is_ok() {
        let _ = state
            .trust_invalidation_tx
            .send(CacheInvalidation::ApiKey(id));
    }
    match result {
        Ok(()) => (StatusCode::OK, Json(json!({"ok": true}))).into_response(),
        Err(crate::admin::audit::AuditError::ReasonTooShort) => (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "reason_too_short"})),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": e.to_string()})),
        )
            .into_response(),
    }
}

#[derive(Deserialize)]
pub struct SetTrustInput {
    pub trust_override: Option<bool>,
    pub spot_check_rate: Option<i32>,
    pub reason: String,
}

pub async fn set_trust(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<SetTrustInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    use sea_orm::EntityTrait;
    let row = match nasrudin_pg::entity::api_keys::Entity::find_by_id(id)
        .one(pg)
        .await
    {
        Ok(Some(r)) => r,
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
    let target_user_id = row.user_id;
    let new_to = body.trust_override;
    let new_rate = body.spot_check_rate;
    let before_to = row.trust_override;
    let before_rate = row.spot_check_rate;
    let result = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta(&headers, addr),
        target_user_id,
        actions::SET_KEY_TRUST,
        body.reason,
        json!({"trust_override": before_to, "spot_check_rate": before_rate}),
        move |txn| {
            Box::pin(async move {
                sea_orm::ConnectionTrait::execute_raw(
                    txn,
                    sea_orm::Statement::from_sql_and_values(
                        sea_orm::DatabaseBackend::Postgres,
                        "UPDATE api_keys SET trust_override=$2, spot_check_rate=$3 WHERE id=$1",
                        [id.into(), new_to.into(), new_rate.into()],
                    ),
                )
                .await?;
                Ok::<_, sea_orm::DbErr>((
                    (),
                    json!({"trust_override": new_to, "spot_check_rate": new_rate}),
                ))
            })
        },
    )
    .await;
    if result.is_ok() {
        let _ = state
            .trust_invalidation_tx
            .send(CacheInvalidation::ApiKey(id));
    }
    match result {
        Ok(()) => (StatusCode::OK, Json(json!({"ok": true}))).into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": e.to_string()})),
        )
            .into_response(),
    }
}
