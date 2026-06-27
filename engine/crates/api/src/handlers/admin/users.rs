//! User-CRUD admin handlers.
//!
//! Every mutating handler:
//! 1. Loads the target row (404 if absent).
//! 2. Refuses to act on self where applicable (admin demotion, etc.).
//! 3. Calls `perform_audited` with a reason ≥ 10 chars.
//! 4. Broadcasts a TrustCache invalidation when relevant.
//!
//! Stripe handles user-facing email for plan changes / subscription
//! events automatically — we do not queue any messaging here.

use std::net::SocketAddr;
use std::sync::Arc;

use axum::{
    Json,
    extract::{ConnectInfo, Path, Query, State},
    http::{HeaderMap, StatusCode},
    response::IntoResponse,
};
use serde::Deserialize;
use serde_json::json;
use uuid::Uuid;

use crate::admin::audit::{AuditError, RequestMeta, actions, perform_audited};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;
use crate::trust::CacheInvalidation;

#[derive(Deserialize)]
pub struct ListParams {
    #[serde(default = "default_page")]
    pub page: u64,
    #[serde(default = "default_page_size")]
    pub page_size: u64,
    pub search: Option<String>,
    #[serde(default)]
    pub only_paid: bool,
}

fn default_page() -> u64 {
    1
}
fn default_page_size() -> u64 {
    25
}

pub async fn list(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Query(p): Query<ListParams>,
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
    match nasrudin_pg::query::admin_users::list_paginated(
        pg,
        p.page,
        p.page_size.min(200),
        p.search.as_deref(),
        p.only_paid,
    )
    .await
    {
        Ok((rows, total)) => (
            StatusCode::OK,
            Json(json!({
                "users": rows,
                "total": total,
                "page": p.page,
                "page_size": p.page_size,
            })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(json!({"error": e.to_string()})),
        )
            .into_response(),
    }
}

pub async fn detail(
    _admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
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
    let user = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
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
    let keys = nasrudin_pg::query::api_keys::list_by_user(pg, id)
        .await
        .unwrap_or_default();
    let audit = nasrudin_pg::query::admin_audit_log::list_by_target(pg, id, 50)
        .await
        .unwrap_or_default();
    (
        StatusCode::OK,
        Json(json!({
            "user": {
                "id": user.id,
                "email": user.email,
                "display_name": user.display_name,
                "plan_tier": user.plan_tier,
                "research_credits": user.research_credits,
                "is_admin": user.is_admin,
                "is_trusted": user.is_trusted,
                "spot_check_rate": user.spot_check_rate,
                "created_at": user.created_at,
                "stripe_customer_id": user.stripe_customer_id,
                "stripe_subscription_id": user.stripe_subscription_id,
                "current_period_end": user.current_period_end,
                "firebase_uid": user.firebase_uid,
            },
            "api_keys": keys,
            "recent_audit": audit,
        })),
    )
        .into_response()
}

// ---------------------------------------------------------------------------
// Mutations
// ---------------------------------------------------------------------------

fn req_meta(headers: &HeaderMap, addr: SocketAddr) -> RequestMeta {
    RequestMeta {
        ip: Some(addr.ip()),
        user_agent: headers
            .get(axum::http::header::USER_AGENT)
            .and_then(|v| v.to_str().ok())
            .map(str::to_string),
    }
}

fn audit_into_response(result: Result<(), AuditError>) -> axum::response::Response {
    match result {
        Ok(()) => (StatusCode::OK, Json(json!({"ok": true}))).into_response(),
        Err(AuditError::ReasonTooShort) => (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "reason_too_short"})),
        )
            .into_response(),
        Err(AuditError::Db(e)) => {
            // P0001 from the prevent_last_admin_demotion trigger surfaces
            // as a Postgres error string; map to 409.
            let s = e.to_string();
            if s.contains("cannot demote last admin") || s.contains("P0001") {
                return (StatusCode::CONFLICT, Json(json!({"error": "last_admin"})))
                    .into_response();
            }
            (StatusCode::INTERNAL_SERVER_ERROR, Json(json!({"error": s}))).into_response()
        }
    }
}

#[derive(Deserialize)]
pub struct SetAdminInput {
    pub is_admin: bool,
    pub reason: String,
}

pub async fn set_admin(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<SetAdminInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    if id == admin.0.user.id {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "cannot_modify_self"})),
        )
            .into_response();
    }
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
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
    let result = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta(&headers, addr),
        Some(id),
        actions::SET_IS_ADMIN,
        body.reason,
        json!({"is_admin": before.is_admin}),
        move |txn| {
            Box::pin(async move {
                nasrudin_pg::query::admin_users::set_is_admin(txn, id, body.is_admin).await?;
                Ok::<_, sea_orm::DbErr>(((), json!({"is_admin": body.is_admin})))
            })
        },
    )
    .await;
    audit_into_response(result)
}

#[derive(Deserialize)]
pub struct SetTrustInput {
    pub is_trusted: bool,
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
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
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
    let result = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta(&headers, addr),
        Some(id),
        actions::SET_IS_TRUSTED,
        body.reason,
        json!({"is_trusted": before.is_trusted}),
        move |txn| {
            Box::pin(async move {
                nasrudin_pg::query::admin_users::set_is_trusted(txn, id, body.is_trusted).await?;
                Ok::<_, sea_orm::DbErr>(((), json!({"is_trusted": body.is_trusted})))
            })
        },
    )
    .await;
    if result.is_ok() {
        let _ = state
            .trust_invalidation_tx
            .send(CacheInvalidation::User(id));
    }
    audit_into_response(result.map(|_| ()))
}

#[derive(Deserialize)]
pub struct SetRateInput {
    pub rate: Option<i32>,
    pub reason: String,
}

pub async fn set_spot_check_rate(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<SetRateInput>,
) -> impl IntoResponse {
    if let Some(r) = body.rate
        && r < 0
    {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "rate_negative"})),
        )
            .into_response();
    }
    let pg = state.pg.as_ref().expect("pg required");
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
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
    let result = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta(&headers, addr),
        Some(id),
        actions::SET_SPOT_CHECK_RATE,
        body.reason,
        json!({"spot_check_rate": before.spot_check_rate}),
        move |txn| {
            Box::pin(async move {
                nasrudin_pg::query::admin_users::set_spot_check_rate(txn, id, body.rate).await?;
                Ok::<_, sea_orm::DbErr>(((), json!({"spot_check_rate": body.rate})))
            })
        },
    )
    .await;
    if result.is_ok() {
        let _ = state
            .trust_invalidation_tx
            .send(CacheInvalidation::User(id));
    }
    audit_into_response(result.map(|_| ()))
}

#[derive(Deserialize)]
pub struct SetPlanInput {
    pub plan_tier: String,
    pub reason: String,
}

pub async fn set_plan(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<SetPlanInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    if !matches!(
        body.plan_tier.as_str(),
        "free" | "researcher" | "team" | "institution"
    ) {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "unknown_tier"})),
        )
            .into_response();
    }
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
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
    let new_tier = body.plan_tier.clone();
    let result = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta(&headers, addr),
        Some(id),
        actions::SET_PLAN_TIER,
        body.reason,
        json!({"plan_tier": &before.plan_tier}),
        move |txn| {
            Box::pin(async move {
                nasrudin_pg::query::admin_users::set_plan_tier(txn, id, &new_tier).await?;
                Ok::<_, sea_orm::DbErr>(((), json!({"plan_tier": new_tier})))
            })
        },
    )
    .await;
    audit_into_response(result.map(|_| ()))
}

#[derive(Deserialize)]
pub struct AdjustCreditsInput {
    pub delta: i32,
    pub reason: String,
}

pub async fn adjust_credits(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<AdjustCreditsInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    let before = match nasrudin_pg::query::admin_users::find_by_id(pg, id).await {
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
    let delta = body.delta;
    let result = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta(&headers, addr),
        Some(id),
        actions::ADJUST_CREDITS,
        body.reason,
        json!({"research_credits": before.research_credits}),
        move |txn| {
            Box::pin(async move {
                let new_credits =
                    nasrudin_pg::query::admin_users::adjust_credits(txn, id, delta).await?;
                Ok::<_, sea_orm::DbErr>((
                    (),
                    json!({"research_credits": new_credits, "delta": delta}),
                ))
            })
        },
    )
    .await;
    audit_into_response(result.map(|_| ()))
}
