//! `/api/billing/*` — Stripe Checkout / Customer Portal / current-plan.
//!
//! The webhook handler is mounted at `/api/billing/webhook` and lives in
//! `crate::billing::webhook`.

use std::sync::Arc;

use axum::{
    Json,
    body::Bytes,
    extract::State,
    http::{HeaderMap, StatusCode},
    response::{IntoResponse, Response},
};
use serde::{Deserialize, Serialize};

use crate::auth::AuthOrApiKey;
use crate::billing::webhook;
use crate::state::AppState;

fn err(status: StatusCode, code: &str) -> Response {
    (status, Json(serde_json::json!({ "error": code }))).into_response()
}

#[derive(Deserialize)]
pub struct CheckoutRequest {
    /// "researcher_monthly" or "researcher_annual" — Phase 1 only sells
    /// the Researcher tier self-serve. Team / Institution / Enterprise
    /// stay on a sales-contact CTA until org-subscriptions ship.
    pub price_key: String,
}

#[derive(Serialize)]
pub struct CheckoutResponse {
    pub url: String,
}

/// `POST /api/billing/checkout` — start a Stripe Checkout session for a
/// subscription. Returns the hosted URL the frontend redirects to.
pub async fn checkout(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    Json(body): Json<CheckoutRequest>,
) -> Response {
    let billing = match &state.billing {
        Some(b) => b,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "billing_unavailable"),
    };
    let pg = match &state.pg {
        Some(p) => p,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable"),
    };

    let price_id = match body.price_key.as_str() {
        "researcher_monthly" => billing.cfg.price_researcher_monthly.clone(),
        "researcher_annual" => billing.cfg.price_researcher_annual.clone(),
        _ => return err(StatusCode::BAD_REQUEST, "unknown_price_key"),
    };

    let user = &auth.user;

    // Reuse an existing Stripe customer if we already created one for this
    // user; otherwise create + persist before opening Checkout.
    let customer_id = match user.stripe_customer_id.clone() {
        Some(c) => c,
        None => {
            let new_id = match billing.create_customer(&user.email, user.id).await {
                Ok(id) => id,
                Err(e) => {
                    tracing::warn!("stripe customer create failed: {e}");
                    return err(StatusCode::BAD_GATEWAY, "stripe_customer_create_failed");
                }
            };
            if let Err(e) =
                nasrudin_pg::query::users::set_stripe_customer_id(pg, user.id, &new_id).await
            {
                tracing::warn!("persist stripe_customer_id failed: {e}");
            }
            new_id
        }
    };

    match billing
        .create_checkout_session(&customer_id, &price_id, user.id)
        .await
    {
        Ok(url) => Json(CheckoutResponse { url }).into_response(),
        Err(e) => {
            tracing::warn!("stripe checkout create failed: {e}");
            err(StatusCode::BAD_GATEWAY, "checkout_create_failed")
        }
    }
}

/// `POST /api/billing/portal` — open the Customer Portal so the user can
/// cancel, change payment method, or view invoices.
pub async fn portal(State(state): State<Arc<AppState>>, auth: AuthOrApiKey) -> Response {
    let billing = match &state.billing {
        Some(b) => b,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "billing_unavailable"),
    };
    let customer_id = match auth.user.stripe_customer_id.as_ref() {
        Some(c) => c.clone(),
        None => return err(StatusCode::BAD_REQUEST, "no_stripe_customer"),
    };
    match billing.create_portal_session(&customer_id).await {
        Ok(url) => Json(serde_json::json!({ "url": url })).into_response(),
        Err(e) => {
            tracing::warn!("stripe portal create failed: {e}");
            err(StatusCode::BAD_GATEWAY, "portal_create_failed")
        }
    }
}

/// `GET /api/billing/me` — current plan + period + remaining quota.
/// Drives the /profile billing card.
pub async fn me(State(state): State<Arc<AppState>>, auth: AuthOrApiKey) -> Response {
    let plan_tier = crate::billing::PlanTier::from_db(&auth.user.plan_tier);
    let q = plan_tier.quotas();
    let now = chrono::Utc::now();
    let cycle_start = auth
        .user
        .plan_cycle_start
        .map(|d| d.with_timezone(&chrono::Utc));
    let period_start = crate::billing::period_start(cycle_start, now);

    let pg = match &state.pg {
        Some(p) => p,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable"),
    };

    let used_searches =
        nasrudin_pg::query::targeted_search_usage::count_in_period(pg, auth.user.id, period_start)
            .await
            .unwrap_or(0);
    let used_today =
        nasrudin_pg::query::api_usage::count_today(pg, auth.user.id, now.date_naive())
            .await
            .unwrap_or(0);

    Json(serde_json::json!({
        "plan_tier": plan_tier.as_db(),
        "current_period_end": auth.user.current_period_end,
        "targeted_searches_used": used_searches,
        "targeted_searches_limit": q.targeted_searches_per_period,
        "api_used_today": used_today,
        "api_limit_per_day": q.api_per_day,
    }))
    .into_response()
}

/// `POST /api/billing/webhook` — Stripe webhook receiver.
///
/// Body must arrive raw (signature is over the bytes), so this handler
/// takes `Bytes` rather than `Json<…>`. Pipeline:
///   1. Verify HMAC over `<timestamp>.<body>`.
///   2. Insert into billing_events keyed by stripe_event_id (idempotent
///      on replay).
///   3. Dispatch by event_type.
///   4. Mark the row processed (with error message if dispatch failed).
///   5. Return 200 on any signature-valid event so Stripe doesn't retry
///      on bugs we'll catch via the unprocessed-events alert.
pub async fn webhook(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    body: Bytes,
) -> Response {
    let billing = match &state.billing {
        Some(b) => b,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "billing_unavailable"),
    };
    let pg = match &state.pg {
        Some(p) => p,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable"),
    };
    let sig_header = match headers
        .get("stripe-signature")
        .and_then(|v| v.to_str().ok())
    {
        Some(s) => s,
        None => return err(StatusCode::BAD_REQUEST, "missing_signature"),
    };

    let event = match webhook::parse_event(&body, sig_header, &billing.cfg.webhook_secret) {
        Ok(e) => e,
        Err(e) => {
            tracing::warn!("webhook signature verify failed: {e}");
            return err(StatusCode::BAD_REQUEST, "invalid_signature");
        }
    };

    // Idempotent insert: if Stripe replayed an event we already processed,
    // return 200 immediately without re-applying side effects.
    let payload_json: serde_json::Value =
        serde_json::from_slice(&body).unwrap_or(serde_json::Value::Null);
    let event_type = format!("{:?}", event.type_);
    let is_new = match nasrudin_pg::query::billing::record_event_if_new(
        pg,
        event.id.as_str(),
        &event_type,
        payload_json,
    )
    .await
    {
        Ok(b) => b,
        Err(e) => {
            tracing::warn!("billing_events insert failed: {e}");
            return (StatusCode::OK, "").into_response();
        }
    };
    if !is_new {
        return (StatusCode::OK, "").into_response();
    }

    let result = webhook::dispatch(&event, &billing.cfg, pg).await;
    let err_msg_owned = result.as_ref().err().map(|e| e.to_string());
    let err_msg = err_msg_owned.as_deref();
    let _ =
        nasrudin_pg::query::billing::mark_event_processed(pg, event.id.as_str(), err_msg).await;
    (StatusCode::OK, "").into_response()
}
