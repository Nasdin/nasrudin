//! Public user-profile endpoints.
//!
//! `GET /api/users/{id}` returns a sanitised view of a user account
//! plus aggregated sponsorship stats. Distinct from
//! `/api/me/profile` (which serves the *signed-in* user their own
//! editable profile, including private fields like email).
//!
//! Public response intentionally excludes:
//! - email, plan_tier, research_credits, firebase_uid, is_admin,
//!   is_trusted, spot_check_rate
//! - per-row stripe_subscription_id / stripe_charge_id (we expose
//!   only the aggregate `sponsorship` summary; individual rows are
//!   never returned to a profile viewer).

use std::sync::Arc;

use axum::{
    Json,
    extract::{Path, State},
    http::StatusCode,
    response::{IntoResponse, Response},
};
use serde::Serialize;
use uuid::Uuid;

use crate::state::AppState;

#[derive(Serialize)]
pub struct PublicSponsorshipSummary {
    pub active_tier: Option<String>,
    pub active_amount_cents: Option<i64>,
    pub lifetime_total_cents: i64,
    pub donation_count: i32,
    pub first_supported_at: Option<chrono::DateTime<chrono::FixedOffset>>,
    pub latest_supported_at: Option<chrono::DateTime<chrono::FixedOffset>>,
}

impl From<nasrudin_pg::query::user_sponsorships::SponsorshipSummary> for PublicSponsorshipSummary {
    fn from(s: nasrudin_pg::query::user_sponsorships::SponsorshipSummary) -> Self {
        let (active_tier, active_amount_cents) = match s.active_subscription {
            Some(t) => (t.tier, t.amount_cents),
            None => (None, None),
        };
        Self {
            active_tier,
            active_amount_cents,
            lifetime_total_cents: s.lifetime_total_cents,
            donation_count: s.donation_count,
            first_supported_at: s.first_supported_at,
            latest_supported_at: s.latest_supported_at,
        }
    }
}

fn err(status: StatusCode, code: &str) -> Response {
    (status, Json(serde_json::json!({ "error": code }))).into_response()
}

/// `GET /api/users/{id}` — public-facing user profile.
pub async fn public_profile(State(state): State<Arc<AppState>>, Path(id): Path<Uuid>) -> Response {
    let pg = match &state.pg {
        Some(p) => p,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable"),
    };
    let user = match nasrudin_pg::query::users::find_by_id(pg, id).await {
        Ok(Some(u)) => u,
        Ok(None) => return err(StatusCode::NOT_FOUND, "user_not_found"),
        Err(e) => {
            tracing::warn!(error = %e, "public_profile lookup failed");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    };

    let summary = nasrudin_pg::query::user_sponsorships::summary_for_user(pg, id)
        .await
        .map(PublicSponsorshipSummary::from)
        .unwrap_or(PublicSponsorshipSummary {
            active_tier: None,
            active_amount_cents: None,
            lifetime_total_cents: 0,
            donation_count: 0,
            first_supported_at: None,
            latest_supported_at: None,
        });

    Json(serde_json::json!({
        "id": user.id,
        "display_name": user.display_name,
        "created_at": user.created_at,
        "sponsorship": summary,
    }))
    .into_response()
}

/// `GET /api/users/{id}/sponsorship` — sponsorship summary as a
/// stand-alone object so the frontend can fetch it without hitting
/// the heavier profile endpoint.
pub async fn public_sponsorship(
    State(state): State<Arc<AppState>>,
    Path(id): Path<Uuid>,
) -> Response {
    let pg = match &state.pg {
        Some(p) => p,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "pg_unavailable"),
    };
    // 404 if the user doesn't exist — distinct from "user has no
    // sponsorships yet" (which returns the zeroed summary).
    match nasrudin_pg::query::users::find_by_id(pg, id).await {
        Ok(Some(_)) => {}
        Ok(None) => return err(StatusCode::NOT_FOUND, "user_not_found"),
        Err(e) => {
            tracing::warn!(error = %e, "sponsorship lookup failed");
            return err(StatusCode::INTERNAL_SERVER_ERROR, "db_error");
        }
    }

    match nasrudin_pg::query::user_sponsorships::summary_for_user(pg, id).await {
        Ok(s) => Json(PublicSponsorshipSummary::from(s)).into_response(),
        Err(e) => {
            tracing::warn!(error = %e, "summary_for_user failed");
            err(StatusCode::INTERNAL_SERVER_ERROR, "db_error")
        }
    }
}
