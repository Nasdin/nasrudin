//! `/api/billing/*` — Stripe Checkout / Customer Portal / current-plan.
//!
//! The webhook handler is mounted at `/api/billing/webhook` and lives in
//! `crate::billing::webhook`.

use std::sync::Arc;

use axum::{
    Json,
    extract::State,
    http::StatusCode,
    response::{IntoResponse, Response},
};
use serde::{Deserialize, Serialize};

use crate::auth::AuthOrApiKey;
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
