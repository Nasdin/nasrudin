//! Firebase-based authentication.
//!
//! Auth flow:
//! 1. The frontend obtains a Firebase ID token (Google sign-in or
//!    email/password via Firebase Auth).
//! 2. It POSTs the token to `/api/auth/firebase-session`.
//! 3. The server verifies the token (RS256 against Google's JWKs),
//!    finds-or-creates the matching `users` row (keyed by `firebase_uid`),
//!    and writes `user_id` into a `tower-sessions` session cookie.
//! 4. Subsequent requests carry the session cookie. The `AuthSess`
//!    extractor reads `user_id` and looks the user up.
//!
//! There is no password DB. Firebase is the source of truth for identity;
//! the PG `users` table is the local mirror that anchors plan/billing/admin
//! state.

use std::sync::Arc;

use axum::extract::FromRequestParts;
use axum::http::{StatusCode, header, request::Parts};
use axum::{Json, response::IntoResponse};
use nasrudin_pg::sea_orm::DatabaseConnection;
use serde::{Deserialize, Serialize};
use tower_sessions::Session;
use uuid::Uuid;

use crate::state::AppState;

/// Session-storage key under which we persist the authenticated user id.
const SESSION_USER_KEY: &str = "user_id";

// ---------------------------------------------------------------------------
// AuthUser
// ---------------------------------------------------------------------------

/// Wrapper around the pg `users::Model`. Carried through request handlers
/// once the session cookie has been resolved.
#[derive(Debug, Clone, Serialize)]
pub struct AuthUser {
    pub id: Uuid,
    pub email: String,
    pub display_name: Option<String>,
    pub created_at: chrono::DateTime<chrono::FixedOffset>,
    pub plan_tier: String,
    pub stripe_customer_id: Option<String>,
    pub stripe_subscription_id: Option<String>,
    pub current_period_end: Option<chrono::DateTime<chrono::FixedOffset>>,
    pub plan_cycle_start: Option<chrono::DateTime<chrono::FixedOffset>>,
    /// Firebase UID — the source-of-truth identity link. Exposed via
    /// /api/auth/me so the frontend can assert "this is the user I think
    /// it is" before issuing API calls.
    pub firebase_uid: String,
}

impl AuthUser {
    pub fn from_model(m: nasrudin_pg::entity::users::Model) -> Self {
        Self {
            id: m.id,
            email: m.email,
            display_name: m.display_name,
            created_at: m.created_at,
            plan_tier: m.plan_tier,
            stripe_customer_id: m.stripe_customer_id,
            stripe_subscription_id: m.stripe_subscription_id,
            current_period_end: m.current_period_end,
            plan_cycle_start: m.plan_cycle_start,
            firebase_uid: m.firebase_uid,
        }
    }
}

// ---------------------------------------------------------------------------
// AuthSess: the cookie-session extractor
// ---------------------------------------------------------------------------

/// Thin handle to the PG connection so handlers can keep using
/// `auth.backend.db` after the axum-login removal. Exists only to
/// preserve the field-access ergonomics of the prior API; conceptually
/// it's the same as `state.pg.as_ref().expect("pg")`.
#[derive(Clone)]
pub struct AuthBackend {
    pub db: DatabaseConnection,
}

/// Extractor that resolves the cookie session into an optional `AuthUser`.
///
/// The handler still runs when nothing is signed in (`user == None`); only
/// `AuthOrApiKey` / `RequireAdmin` reject unauthenticated requests.
///
/// Always succeeds at the extractor level so callers can decide whether
/// to demand a user or keep the request public.
pub struct AuthSess {
    pub user: Option<AuthUser>,
    pub session: Session,
    /// Compatibility handle for handlers that read `auth.backend.db` —
    /// kept verbatim during the axum-login removal so existing call
    /// sites need no edits.
    pub backend: AuthBackend,
}

impl AuthSess {
    /// Persist `user.id` into the cookie session, returning the populated
    /// `AuthUser`. Mirrors what `axum_login::AuthSession::login` used to do.
    pub async fn install(&mut self, user: AuthUser) -> Result<AuthUser, tower_sessions::session::Error> {
        // Cycle the session ID on login so a pre-auth fixation token can't
        // be reused post-auth (defence-in-depth; tower-sessions's default
        // cookie scope already mitigates this).
        self.session.cycle_id().await?;
        self.session.insert(SESSION_USER_KEY, user.id).await?;
        self.user = Some(user.clone());
        Ok(user)
    }

    /// Clear the cookie session. Returns `Ok(())` even if no user was
    /// signed in.
    pub async fn logout(&mut self) -> Result<(), tower_sessions::session::Error> {
        self.session.flush().await?;
        self.user = None;
        Ok(())
    }
}

impl FromRequestParts<Arc<AppState>> for AuthSess {
    type Rejection = (StatusCode, Json<serde_json::Value>);

    async fn from_request_parts(
        parts: &mut Parts,
        state: &Arc<AppState>,
    ) -> Result<Self, Self::Rejection> {
        let session = Session::from_request_parts(parts, state)
            .await
            .map_err(|_| session_unavailable())?;
        let pg = state.pg.as_ref().ok_or_else(pg_unavailable)?;
        let user = resolve_user_from_session(&session, Some(pg)).await;
        Ok(Self {
            user,
            session,
            backend: AuthBackend { db: pg.clone() },
        })
    }
}

fn pg_unavailable() -> (StatusCode, Json<serde_json::Value>) {
    (
        StatusCode::SERVICE_UNAVAILABLE,
        Json(serde_json::json!({ "error": "pg_unavailable" })),
    )
}

async fn resolve_user_from_session(
    session: &Session,
    pg: Option<&DatabaseConnection>,
) -> Option<AuthUser> {
    let uid: Uuid = session.get(SESSION_USER_KEY).await.ok().flatten()?;
    let pg = pg?;
    nasrudin_pg::query::users::find_by_id(pg, uid)
        .await
        .ok()
        .flatten()
        .map(AuthUser::from_model)
}

fn session_unavailable() -> (StatusCode, Json<serde_json::Value>) {
    (
        StatusCode::INTERNAL_SERVER_ERROR,
        Json(serde_json::json!({ "error": "session_unavailable" })),
    )
}

// ---------------------------------------------------------------------------
// Handlers
// ---------------------------------------------------------------------------

/// `POST /api/auth/logout`
pub async fn logout(mut auth_session: AuthSess) -> impl IntoResponse {
    if let Err(e) = auth_session.logout().await {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("logout error: {e}") })),
        );
    }
    (
        StatusCode::OK,
        Json(serde_json::json!({ "logged_out": true })),
    )
}

/// `GET /api/auth/me`
pub async fn me(auth_session: AuthSess) -> impl IntoResponse {
    match auth_session.user {
        Some(ref user) => (StatusCode::OK, Json(serde_json::to_value(user).unwrap())),
        None => (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "Not authenticated" })),
        ),
    }
}

// ---------------------------------------------------------------------------
// Firebase session-exchange
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
pub struct FirebaseSessionInput {
    pub id_token: String,
}

/// `POST /api/auth/firebase-session`
///
/// Verifies a Firebase ID token (RS256 JWT against Google's JWKs),
/// find-or-creates the matching `users` row keyed by `firebase_uid`, and
/// writes `user_id` into the cookie session. The Firebase ID token is
/// consumed once and not stored.
///
/// Strict-verification policy: rejects `email_verified == false` for the
/// `password` provider only. Google-provider sign-ins pass through (Google
/// guarantees the email is verified).
pub async fn firebase_session(
    axum::extract::State(state): axum::extract::State<std::sync::Arc<crate::state::AppState>>,
    mut auth_session: AuthSess,
    Json(body): Json<FirebaseSessionInput>,
) -> axum::response::Response {
    use axum::response::IntoResponse as _;

    let Some(ref project_id) = state.firebase_project_id else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "firebase_not_configured" })),
        )
            .into_response();
    };

    // 1. Verify the token.
    let claims = match crate::firebase_auth::verify_id_token(
        &body.id_token,
        project_id,
        &state.firebase_jwks,
    )
    .await
    {
        Ok(c) => c,
        Err(e) => {
            let (code, msg) = match e {
                crate::firebase_auth::VerifyError::Expired => ("token_expired", "id token expired"),
                crate::firebase_auth::VerifyError::WrongAudience => {
                    ("wrong_audience", "id token aud mismatch")
                }
                crate::firebase_auth::VerifyError::WrongIssuer => {
                    ("wrong_issuer", "id token iss mismatch")
                }
                crate::firebase_auth::VerifyError::BadSignature => {
                    ("bad_signature", "id token signature invalid")
                }
                crate::firebase_auth::VerifyError::MalformedToken(_) => {
                    ("malformed_token", "id token malformed")
                }
                crate::firebase_auth::VerifyError::MissingClaim(c) => {
                    tracing::warn!(claim = c, "firebase id token missing required claim");
                    ("missing_claim", "id token missing required claim")
                }
                crate::firebase_auth::VerifyError::JwksFetch(_) => {
                    return (
                        StatusCode::BAD_GATEWAY,
                        Json(serde_json::json!({ "error": "jwks_unavailable" })),
                    )
                        .into_response();
                }
            };
            tracing::info!(error = msg, "firebase_session verify failed");
            return (
                StatusCode::UNAUTHORIZED,
                Json(serde_json::json!({ "error": code })),
            )
                .into_response();
        }
    };

    // 2. Strict email-verification policy: only enforce for password provider.
    if !claims.email_verified && claims.sign_in_provider == "password" {
        return (
            StatusCode::FORBIDDEN,
            Json(serde_json::json!({ "error": "email_not_verified" })),
        )
            .into_response();
    }

    // 3. Find or create user.
    let db = &auth_session.backend.db;
    let user_model = match nasrudin_pg::query::users::find_by_firebase_uid(db, &claims.uid).await {
        Ok(Some(m)) => m,
        Ok(None) => match nasrudin_pg::query::users::create_firebase_user(
            db,
            &claims.uid,
            &claims.email,
            claims.name.as_deref(),
        )
        .await
        {
            Ok(m) => m,
            Err(e) => {
                tracing::error!(error = %e, "create_firebase_user failed");
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(serde_json::json!({ "error": "user_create_failed" })),
                )
                    .into_response();
            }
        },
        Err(e) => {
            tracing::error!(error = %e, "find_by_firebase_uid failed");
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": "db_lookup_failed" })),
            )
                .into_response();
        }
    };

    let auth_user = AuthUser::from_model(user_model);

    // 4. Issue session cookie.
    if let Err(e) = auth_session.install(auth_user.clone()).await {
        tracing::error!(error = %e, "session install failed");
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": "session_create_failed" })),
        )
            .into_response();
    }

    (StatusCode::OK, Json(serde_json::to_value(&auth_user).unwrap())).into_response()
}

// ---------------------------------------------------------------------------
// AuthOrApiKey: cookie session OR `Authorization: Bearer nsk_live_…`
// ---------------------------------------------------------------------------

/// Extractor that succeeds for both authenticated cookie sessions
/// and valid `Authorization: Bearer nsk_live_<secret>` tokens.
///
/// Worker keys (`kind == "worker"`) are explicitly rejected — they must use
/// the `WorkerAuth` extractor instead.
pub struct AuthOrApiKey {
    pub user: AuthUser,
}

impl FromRequestParts<Arc<AppState>> for AuthOrApiKey {
    type Rejection = (StatusCode, axum::Json<serde_json::Value>);

    async fn from_request_parts(
        parts: &mut Parts,
        state: &Arc<AppState>,
    ) -> Result<Self, Self::Rejection> {
        // 0. Impersonation: if the request carries an active impersonation
        //    token, the `impersonation_layer` middleware has already injected
        //    the target's `AuthUser` into request extensions. Use it.
        if let Some(target) = parts.extensions.get::<AuthUser>() {
            return Ok(Self {
                user: target.clone(),
            });
        }

        // 1. Try cookie session.
        if let Ok(sess) = AuthSess::from_request_parts(parts, state).await
            && let Some(user) = sess.user
        {
            return Ok(Self { user });
        }

        // 2. Fall back to bearer token.
        let bearer: String = parts
            .headers
            .get(header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.strip_prefix("Bearer "))
            .map(|s| s.to_owned())
            .ok_or_else(unauth_response)?;

        if !bearer.starts_with("nsk_live_") {
            return Err(unauth_response());
        }

        let db = state.pg.as_ref().ok_or_else(unauth_response)?;

        let prefix: String = bearer.chars().take(12).collect();
        let row = nasrudin_pg::query::api_keys::find_by_prefix(db, &prefix)
            .await
            .map_err(|_| unauth_response())?
            .ok_or_else(unauth_response)?;

        if row.kind != "live" {
            return Err(unauth_response());
        }
        if let Some(exp) = row.expires_at
            && exp < chrono::Utc::now()
        {
            return Err(expired_response());
        }
        let secret = bearer.to_owned();
        let hash = row.key_hash.clone();
        let valid = tokio::task::spawn_blocking(move || {
            password_auth::verify_password(secret, &hash).is_ok()
        })
        .await
        .map_err(|_| unauth_response())?;
        if !valid {
            return Err(unauth_response());
        }

        // Mark used (best-effort, fire and forget)
        let db_clone = db.clone();
        let key_id = row.id;
        tokio::spawn(async move {
            let _ = nasrudin_pg::query::api_keys::mark_used(&db_clone, key_id).await;
        });

        let user_id = row.user_id.ok_or_else(unauth_response)?;
        let user_model = nasrudin_pg::query::users::find_by_id(db, user_id)
            .await
            .map_err(|_| unauth_response())?
            .ok_or_else(unauth_response)?;

        Ok(Self {
            user: AuthUser::from_model(user_model),
        })
    }
}

fn unauth_response() -> (StatusCode, axum::Json<serde_json::Value>) {
    (
        StatusCode::UNAUTHORIZED,
        axum::Json(serde_json::json!({ "error": "not authenticated" })),
    )
}

fn expired_response() -> (StatusCode, axum::Json<serde_json::Value>) {
    (
        StatusCode::UNAUTHORIZED,
        axum::Json(serde_json::json!({ "error": "expired api key" })),
    )
}

// ---------------------------------------------------------------------------
// WorkerAuth: only `Authorization: Bearer nsk_worker_…`
// ---------------------------------------------------------------------------

/// Resolved identity of a worker (no `AuthUser` — workers are not users).
#[derive(Debug, Clone)]
pub struct WorkerCredential {
    pub api_key_id: uuid::Uuid,
    /// The associated `workers.id` row (set by the registration handler;
    /// we look it up via `name` which is the worker handle).
    pub worker_handle: String,
}

pub struct WorkerAuth(pub WorkerCredential);

impl FromRequestParts<Arc<AppState>> for WorkerAuth {
    type Rejection = (StatusCode, axum::Json<serde_json::Value>);

    async fn from_request_parts(
        parts: &mut Parts,
        state: &Arc<AppState>,
    ) -> Result<Self, Self::Rejection> {
        let bearer: String = parts
            .headers
            .get(header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.strip_prefix("Bearer "))
            .map(|s| s.to_owned())
            .ok_or_else(unauth_response)?;
        // Non-worker bearer prefixes are *forbidden* (the caller authenticated
        // successfully but presented a key of the wrong kind). 403, not 401.
        if !bearer.starts_with("nsk_worker_") {
            return Err(forbidden_non_worker());
        }

        let db = state.pg.as_ref().ok_or_else(unauth_response)?;

        let prefix: String = bearer.chars().take(14).collect();
        let row = nasrudin_pg::query::api_keys::find_by_prefix(db, &prefix)
            .await
            .map_err(|_| unauth_response())?
            .ok_or_else(unauth_response)?;
        if row.kind != "worker" {
            return Err(forbidden_non_worker());
        }

        let secret = bearer.to_owned();
        let hash = row.key_hash.clone();
        let valid = tokio::task::spawn_blocking(move || {
            password_auth::verify_password(secret, &hash).is_ok()
        })
        .await
        .map_err(|_| unauth_response())?;
        if !valid {
            return Err(unauth_response());
        }

        Ok(Self(WorkerCredential {
            api_key_id: row.id,
            worker_handle: row.name,
        }))
    }
}

fn forbidden_non_worker() -> (StatusCode, axum::Json<serde_json::Value>) {
    (
        StatusCode::FORBIDDEN,
        axum::Json(serde_json::json!({ "error": "non_worker_key" })),
    )
}
