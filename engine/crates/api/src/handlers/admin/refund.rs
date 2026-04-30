//! `POST /api/admin/users/{id}/refund` — DB-first → Stripe-second flow.
//!
//! Stripe handles the user-facing email automatically. The admin sees
//! the result in the response body and via the audit log.

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

use crate::admin::audit::{actions, perform_audited, RequestMeta};
use crate::admin::require_admin::RequireAdmin;
use crate::state::AppState;

#[derive(Deserialize)]
pub struct RefundInput {
    pub stripe_charge_id: String,
    pub amount_cents: i64,
    pub reason: String,
}

pub async fn refund(
    admin: RequireAdmin,
    State(state): State<Arc<AppState>>,
    Path(user_id): Path<Uuid>,
    headers: HeaderMap,
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    Json(body): Json<RefundInput>,
) -> impl IntoResponse {
    let pg = state.pg.as_ref().expect("pg required");
    if body.amount_cents <= 0 {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "amount_must_be_positive"})),
        )
            .into_response();
    }

    // Verify the charge belongs to this user.
    let user = match nasrudin_pg::query::admin_users::find_by_id(pg, user_id).await {
        Ok(Some(u)) => u,
        Ok(None) => {
            return (StatusCode::NOT_FOUND, Json(json!({"error": "not_found"})))
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
    let charge = match crate::billing::refund::fetch_charge(
        &state.stripe_http,
        &state.stripe_base_url,
        &state.stripe_secret,
        &body.stripe_charge_id,
    )
    .await
    {
        Ok(Some(c)) => c,
        Ok(None) => {
            return (
                StatusCode::UNPROCESSABLE_ENTITY,
                Json(json!({"error": "charge_not_found"})),
            )
                .into_response();
        }
        Err(e) => {
            return (
                StatusCode::BAD_GATEWAY,
                Json(json!({"error": e.to_string()})),
            )
                .into_response();
        }
    };
    if user.stripe_customer_id.as_deref() != charge.customer.as_deref() {
        return (
            StatusCode::UNPROCESSABLE_ENTITY,
            Json(json!({"error": "charge_belongs_to_other_customer"})),
        )
            .into_response();
    }

    // 1) DB-first: insert pending refund + audit row in one txn.
    let admin_id = admin.0.user.id;
    let amount_cents = body.amount_cents as i32;
    let currency = charge.currency.clone();
    let charge_id = body.stripe_charge_id.clone();
    let req_meta = RequestMeta {
        ip: Some(addr.ip()),
        user_agent: headers
            .get(axum::http::header::USER_AGENT)
            .and_then(|v| v.to_str().ok())
            .map(str::to_string),
    };
    let reason = body.reason.clone();
    let charge_for_log = charge_id.clone();

    let refund_id_result: Result<Uuid, _> = perform_audited(
        pg,
        &admin.0.user,
        None,
        req_meta,
        Some(user_id),
        actions::REFUND_INITIATED,
        body.reason,
        json!({"charge_id": &charge_for_log, "amount_cents": amount_cents}),
        move |txn| {
            Box::pin(async move {
                let id = nasrudin_pg::query::refund_records::insert(
                    txn,
                    user_id,
                    admin_id,
                    &charge_id,
                    amount_cents,
                    &currency,
                    &reason,
                )
                .await?;
                Ok::<_, sea_orm::DbErr>((id, json!({"refund_record_id": id})))
            })
        },
    )
    .await;
    let refund_id = match refund_id_result {
        Ok(id) => id,
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

    // 2) Stripe-second.
    match crate::billing::refund::create_refund(
        &state.stripe_http,
        &state.stripe_base_url,
        &state.stripe_secret,
        &body.stripe_charge_id,
        body.amount_cents,
        refund_id,
        refund_id,
    )
    .await
    {
        Ok(resp) => {
            let _ =
                nasrudin_pg::query::refund_records::mark_succeeded(pg, refund_id, &resp.id).await;
            (
                StatusCode::OK,
                Json(json!({
                    "refund_id": resp.id,
                    "status": resp.status,
                    "record_id": refund_id,
                })),
            )
                .into_response()
        }
        Err(e) => {
            let msg = e.to_string();
            if msg.starts_with("4xx") {
                let _ = nasrudin_pg::query::refund_records::mark_failed(pg, refund_id, &msg).await;
                (
                    StatusCode::UNPROCESSABLE_ENTITY,
                    Json(json!({"error": msg, "record_id": refund_id})),
                )
                    .into_response()
            } else {
                // Transient / network. Leave pending for the reconciler.
                tracing::warn!(
                    refund_id = %refund_id,
                    error = %msg,
                    "refund Stripe call failed transiently; reconciler will resolve"
                );
                (
                    StatusCode::ACCEPTED,
                    Json(json!({
                        "record_id": refund_id,
                        "status": "pending",
                        "note": "reconciler_will_resolve",
                    })),
                )
                    .into_response()
            }
        }
    }
}
