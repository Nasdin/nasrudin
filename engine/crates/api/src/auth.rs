//! Authentication module: axum-login backend, session handlers.

use axum::{
    http::StatusCode,
    response::IntoResponse,
    Json,
};
use axum_login::{AuthSession, AuthnBackend};
use nasrudin_pg::sea_orm::{DatabaseConnection, DbErr};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

// ---------------------------------------------------------------------------
// AuthUser
// ---------------------------------------------------------------------------

/// Wrapper around the pg `users::Model` that implements `axum_login::AuthUser`.
#[derive(Debug, Clone, Serialize)]
pub struct AuthUser {
    pub id: Uuid,
    pub email: String,
    #[serde(skip)]
    pub password_hash: String,
    pub display_name: Option<String>,
    pub created_at: chrono::DateTime<chrono::FixedOffset>,
}

impl AuthUser {
    fn from_model(m: nasrudin_pg::entity::users::Model) -> Self {
        Self {
            id: m.id,
            email: m.email,
            password_hash: m.password_hash,
            display_name: m.display_name,
            created_at: m.created_at,
        }
    }
}

impl axum_login::AuthUser for AuthUser {
    type Id = Uuid;

    fn id(&self) -> Uuid {
        self.id
    }

    fn session_auth_hash(&self) -> &[u8] {
        self.password_hash.as_bytes()
    }
}

// ---------------------------------------------------------------------------
// Credentials
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Deserialize)]
pub struct Credentials {
    pub email: String,
    pub password: String,
}

// ---------------------------------------------------------------------------
// Backend
// ---------------------------------------------------------------------------

/// Auth backend backed by the PostgreSQL `users` table.
#[derive(Debug, Clone)]
pub struct Backend {
    db: DatabaseConnection,
}

impl Backend {
    pub fn new(db: DatabaseConnection) -> Self {
        Self { db }
    }
}

/// Newtype so we can implement `std::error::Error` + `IntoResponse`.
#[derive(Debug, thiserror::Error)]
pub enum AuthError {
    #[error("database error: {0}")]
    Db(#[from] DbErr),

    #[error("task join error: {0}")]
    TaskJoin(#[from] tokio::task::JoinError),
}

impl AuthnBackend for Backend {
    type User = AuthUser;
    type Credentials = Credentials;
    type Error = AuthError;

    async fn authenticate(
        &self,
        creds: Self::Credentials,
    ) -> Result<Option<Self::User>, Self::Error> {
        let user = nasrudin_pg::query::users::find_by_email(&self.db, &creds.email).await?;

        let Some(user) = user else {
            return Ok(None);
        };

        // Argon2 verification is CPU-intensive — run on blocking thread.
        let hash = user.password_hash.clone();
        let password = creds.password;
        let valid = tokio::task::spawn_blocking(move || {
            password_auth::verify_password(password, &hash).is_ok()
        })
        .await?;

        if valid {
            Ok(Some(AuthUser::from_model(user)))
        } else {
            Ok(None)
        }
    }

    async fn get_user(
        &self,
        user_id: &Uuid,
    ) -> Result<Option<Self::User>, Self::Error> {
        let user = nasrudin_pg::query::users::find_by_id(&self.db, *user_id).await?;
        Ok(user.map(AuthUser::from_model))
    }
}

// Convenience alias.
pub type AuthSess = AuthSession<Backend>;

// ---------------------------------------------------------------------------
// Handlers
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
pub struct RegisterInput {
    pub email: String,
    pub password: String,
    pub display_name: Option<String>,
}

/// `POST /api/auth/register`
pub async fn register(
    mut auth_session: AuthSess,
    Json(body): Json<RegisterInput>,
) -> impl IntoResponse {
    // Hash the password (CPU-intensive).
    let password = body.password.clone();
    let hash = match tokio::task::spawn_blocking(move || {
        password_auth::generate_hash(password)
    })
    .await
    {
        Ok(h) => h,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("hash error: {e}") })),
            );
        }
    };

    // Insert user into DB.
    let db = auth_session.backend.db.clone();
    let user = match nasrudin_pg::query::users::create_user(
        &db,
        &body.email,
        &hash,
        body.display_name.as_deref(),
    )
    .await
    {
        Ok(model) => AuthUser::from_model(model),
        Err(e) => {
            let status = if e.to_string().contains("duplicate") || e.to_string().contains("unique") {
                StatusCode::CONFLICT
            } else {
                StatusCode::INTERNAL_SERVER_ERROR
            };
            return (
                status,
                Json(serde_json::json!({ "error": format!("{e}") })),
            );
        }
    };

    // Auto-login after registration.
    if let Err(e) = auth_session.login(&user).await {
        tracing::error!("Auto-login after register failed: {e}");
    }

    (StatusCode::OK, Json(serde_json::to_value(&user).unwrap()))
}

/// `POST /api/auth/login`
pub async fn login(mut auth_session: AuthSess, Json(body): Json<Credentials>) -> impl IntoResponse {
    match auth_session.authenticate(body).await {
        Ok(Some(user)) => {
            if let Err(e) = auth_session.login(&user).await {
                return (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(serde_json::json!({ "error": format!("session error: {e}") })),
                );
            }
            (StatusCode::OK, Json(serde_json::to_value(&user).unwrap()))
        }
        Ok(None) => (
            StatusCode::UNAUTHORIZED,
            Json(serde_json::json!({ "error": "Invalid email or password" })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("{e}") })),
        ),
    }
}

/// `POST /api/auth/logout`
pub async fn logout(mut auth_session: AuthSess) -> impl IntoResponse {
    if let Err(e) = auth_session.logout().await {
        return (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": format!("logout error: {e}") })),
        );
    }
    (StatusCode::OK, Json(serde_json::json!({ "logged_out": true })))
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
// AuthOrApiKey: cookie session OR `Authorization: Bearer nsk_live_…`
// ---------------------------------------------------------------------------

use axum::{
    extract::FromRequestParts,
    http::{header, request::Parts},
};

/// Extractor that succeeds for both authenticated cookie sessions
/// and valid `Authorization: Bearer nsk_live_<secret>` tokens.
///
/// Worker keys (`kind == "worker"`) are explicitly rejected — they must use
/// the `WorkerAuth` extractor instead.
pub struct AuthOrApiKey {
    pub user: AuthUser,
}

impl<S> FromRequestParts<S> for AuthOrApiKey
where
    S: Send + Sync,
{
    type Rejection = (StatusCode, axum::Json<serde_json::Value>);

    async fn from_request_parts(parts: &mut Parts, state: &S) -> Result<Self, Self::Rejection> {
        // 1. Try cookie session.
        if let Ok(session) = AuthSession::<Backend>::from_request_parts(parts, state).await
            && let Some(user) = session.user
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

        // The cookie-session attempt above already loaded the AuthSession,
        // which carries a clone of the DatabaseConnection in `backend.db`.
        // Re-extract just to grab `db` for the lookup.
        let session = AuthSession::<Backend>::from_request_parts(parts, state)
            .await
            .map_err(|_| unauth_response())?;
        let db: &DatabaseConnection = &session.backend.db;

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

impl<S> FromRequestParts<S> for WorkerAuth
where
    S: Send + Sync,
{
    type Rejection = (StatusCode, axum::Json<serde_json::Value>);

    async fn from_request_parts(parts: &mut Parts, state: &S) -> Result<Self, Self::Rejection> {
        let bearer: String = parts
            .headers
            .get(header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.strip_prefix("Bearer "))
            .map(|s| s.to_owned())
            .ok_or_else(unauth_response)?;
        if !bearer.starts_with("nsk_worker_") {
            return Err(unauth_response());
        }

        let session = AuthSession::<Backend>::from_request_parts(parts, state)
            .await
            .map_err(|_| unauth_response())?;
        let db: &DatabaseConnection = &session.backend.db;

        let prefix: String = bearer.chars().take(14).collect();
        let row = nasrudin_pg::query::api_keys::find_by_prefix(db, &prefix)
            .await
            .map_err(|_| unauth_response())?
            .ok_or_else(unauth_response)?;
        if row.kind != "worker" {
            return Err(unauth_response());
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
