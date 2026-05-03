//! `RequireAdmin` extractor.
//!
//! Two paths to admin access:
//! 1. **Session.** A logged-in user whose `users.is_admin = TRUE`.
//! 2. **Bearer.** `Authorization: Bearer $ADMIN_TOKEN` — used by ops
//!    scripts and the bootstrap reconciler. Synthesizes a `SYSTEM_ACTOR`
//!    AuthUser so audit rows still have a real `actor_user_id`.
//!
//! Returns 401 when neither path applies. 403 (forbidden) when a session
//! is present but the user is not admin.

use std::sync::Arc;

use axum::Json;
use axum::extract::{FromRequestParts, OptionalFromRequestParts};
use axum::http::{StatusCode, header, request::Parts};
use serde_json::json;

use crate::admin::audit::SYSTEM_ACTOR_ID;
use crate::auth::{AuthSess, AuthUser};
use crate::state::AppState;

#[derive(Clone, Debug)]
pub enum AdminAuthSource {
    Session,
    BearerToken,
}

#[derive(Clone, Debug)]
pub struct AdminContext {
    pub user: AuthUser,
    pub source: AdminAuthSource,
}

pub struct RequireAdmin(pub AdminContext);

impl FromRequestParts<Arc<AppState>> for RequireAdmin {
    type Rejection = (StatusCode, Json<serde_json::Value>);

    async fn from_request_parts(
        parts: &mut Parts,
        state: &Arc<AppState>,
    ) -> Result<Self, Self::Rejection> {
        // Path 2 (cheaper): bearer token. Check this before resolving
        // the cookie session so admin scripts/cron don't pay session-store
        // overhead.
        if let Some(provided) = parts
            .headers
            .get(header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.strip_prefix("Bearer "))
        {
            if let Some(expected) = state.admin_token.as_deref()
                && !expected.is_empty()
                && provided == expected
            {
                let now: chrono::DateTime<chrono::FixedOffset> = chrono::Utc::now().into();
                let user = AuthUser {
                    id: SYSTEM_ACTOR_ID,
                    email: "system@nasrudin.org".into(),
                    display_name: Some("system".into()),
                    created_at: now,
                    plan_tier: "free".into(),
                    stripe_customer_id: None,
                    stripe_subscription_id: None,
                    current_period_end: None,
                    plan_cycle_start: None,
                    research_credits: 0,
                    firebase_uid: "system".into(),
                    country_code: None,
                };
                return Ok(RequireAdmin(AdminContext {
                    user,
                    source: AdminAuthSource::BearerToken,
                }));
            }
            // Bearer header present but doesn't match — don't fall
            // through to session, that would be confusing. 401.
            return Err((
                StatusCode::UNAUTHORIZED,
                Json(json!({ "error": "bad_admin_token" })),
            ));
        }

        // Path 1: session.
        if let Ok(sess) = AuthSess::from_request_parts(parts, state).await
            && let Some(user) = sess.user.clone()
        {
            let pg = state.pg.as_ref().ok_or((
                StatusCode::SERVICE_UNAVAILABLE,
                Json(json!({ "error": "pg_unavailable" })),
            ))?;
            let model = nasrudin_pg::query::users::find_by_id(pg, user.id)
                .await
                .map_err(|_| {
                    (
                        StatusCode::INTERNAL_SERVER_ERROR,
                        Json(json!({ "error": "db_error" })),
                    )
                })?;
            let is_admin = model.map(|u| u.is_admin).unwrap_or(false);
            if is_admin {
                return Ok(RequireAdmin(AdminContext {
                    user,
                    source: AdminAuthSource::Session,
                }));
            }
            return Err((
                StatusCode::FORBIDDEN,
                Json(json!({ "error": "admin_required" })),
            ));
        }

        Err((
            StatusCode::UNAUTHORIZED,
            Json(json!({ "error": "admin_required" })),
        ))
    }
}

/// Lets handlers accept `Option<RequireAdmin>` to express "elevate behavior
/// when the caller is admin, otherwise serve the public default." Any
/// rejection from the underlying extractor (no session, bad token, not
/// admin) collapses to `None` instead of failing the request.
impl OptionalFromRequestParts<Arc<AppState>> for RequireAdmin {
    type Rejection = std::convert::Infallible;

    async fn from_request_parts(
        parts: &mut Parts,
        state: &Arc<AppState>,
    ) -> Result<Option<Self>, Self::Rejection> {
        Ok(<Self as FromRequestParts<Arc<AppState>>>::from_request_parts(parts, state)
            .await
            .ok())
    }
}
