//! Per-day API quota middleware.
//!
//! Increments `api_usage_daily.request_count` atomically on every
//! authenticated request and returns 429 when today's count exceeds the
//! caller's `PlanTier::quotas().api_per_day`. Cheap on the hot path —
//! one upsert returning the post-increment count.
//!
//! Skipped when AppState.pg is None (dev without Postgres) — no usage to
//! track and no auth user to charge.

use std::sync::Arc;

use axum::{
    Json,
    body::Body,
    extract::{Request, State},
    http::StatusCode,
    middleware::Next,
    response::{IntoResponse, Response},
};

use crate::auth::AuthOrApiKey;
use crate::billing::PlanTier;
use crate::state::AppState;

pub async fn api_quota(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    req: Request<Body>,
    next: Next,
) -> Response {
    let pg = match &state.pg {
        Some(p) => p,
        None => return next.run(req).await,
    };
    let plan_tier = PlanTier::from_db(&auth.user.plan_tier);
    let quota = plan_tier.quotas().api_per_day;
    let today = chrono::Utc::now().date_naive();

    match nasrudin_pg::query::api_usage::increment_and_get(pg, auth.user.id, today).await {
        Ok(count) if count as u64 > quota as u64 => (
            StatusCode::TOO_MANY_REQUESTS,
            Json(serde_json::json!({
                "error": "api_quota_exhausted",
                "limit_per_day": quota,
                "plan_tier": plan_tier.as_db(),
            })),
        )
            .into_response(),
        // On DB error don't block the user — alarm in tracing and let
        // them through. Quotas are a soft cost-control, not a hard
        // safety boundary.
        Ok(_) => next.run(req).await,
        Err(e) => {
            tracing::warn!("api_quota increment failed: {e}");
            next.run(req).await
        }
    }
}
