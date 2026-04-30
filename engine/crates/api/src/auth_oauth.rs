//! GitHub OAuth handlers — authorization-code flow on top of axum-login.
//!
//! See spec at
//! `docs/superpowers/specs/2026-04-30-real-signin-and-github-oauth-design.md`.
//!
//! Two endpoints:
//!   - `GET /api/auth/github/start`    — issue state, redirect to github.com
//!   - `GET /api/auth/github/callback` — verify state, exchange code, sign in
//!
//! Both return 503 when `oauth_github` is unconfigured. State is stored
//! in a 5-minute cookie, not server-side, so dev restarts don't break
//! in-flight flows. The cookie is HttpOnly + SameSite=Lax + Secure when
//! behind TLS (toggled via the `OAUTH_COOKIE_SECURE` env var; default
//! true in production-like deployments).

use std::sync::Arc;

use axum::{
    Json,
    extract::{Query, State},
    http::{StatusCode, header},
    response::{IntoResponse, Redirect, Response},
};
use axum_extra::extract::cookie::{Cookie, CookieJar, SameSite};
use oauth2::{
    AuthUrl, AuthorizationCode, ClientId, ClientSecret, CsrfToken, RedirectUrl, Scope,
    TokenResponse, TokenUrl, basic::BasicClient, reqwest::async_http_client,
};
use rand::RngCore;
use serde::Deserialize;

use crate::auth::{AuthSess, AuthUser};
use crate::state::{AppState, GithubOAuthConfig};

const STATE_COOKIE: &str = "github_oauth_state";
const STATE_TTL_SECS: i64 = 300;

fn cookie_secure() -> bool {
    std::env::var("OAUTH_COOKIE_SECURE")
        .map(|v| !matches!(v.trim(), "0" | "false" | "no"))
        .unwrap_or(true)
}

fn oauth_unconfigured() -> Response {
    (
        StatusCode::SERVICE_UNAVAILABLE,
        Json(serde_json::json!({ "error": "oauth_not_configured" })),
    )
        .into_response()
}

fn build_client(cfg: &GithubOAuthConfig) -> BasicClient {
    BasicClient::new(
        ClientId::new(cfg.client_id.clone()),
        Some(ClientSecret::new(cfg.client_secret.clone())),
        AuthUrl::new("https://github.com/login/oauth/authorize".into())
            .expect("valid authorize url"),
        Some(
            TokenUrl::new("https://github.com/login/oauth/access_token".into())
                .expect("valid token url"),
        ),
    )
    .set_redirect_uri(
        RedirectUrl::new(cfg.redirect_uri.clone()).expect("valid redirect url"),
    )
}

/// `GET /api/auth/github/start` — sets a state cookie and 302s to GitHub.
pub async fn start(State(state): State<Arc<AppState>>, jar: CookieJar) -> Response {
    let Some(ref cfg) = state.oauth_github else {
        return oauth_unconfigured();
    };

    let client = build_client(cfg);

    // Generate state and a fresh authorize URL.
    let mut state_bytes = [0u8; 32];
    rand::thread_rng().fill_bytes(&mut state_bytes);
    let state_value = data_encoding::BASE64URL_NOPAD.encode(&state_bytes);

    let (auth_url, _csrf) = client
        .authorize_url(|| CsrfToken::new(state_value.clone()))
        .add_scope(Scope::new("read:user".into()))
        .add_scope(Scope::new("user:email".into()))
        .url();

    let cookie = Cookie::build((STATE_COOKIE, state_value.clone()))
        .http_only(true)
        .same_site(SameSite::Lax)
        .secure(cookie_secure())
        .path("/")
        // axum-extra reexports the `time` crate; cookie max_age uses
        // time::Duration not std::time::Duration.
        .max_age(::time::Duration::seconds(STATE_TTL_SECS))
        .build();

    let jar = jar.add(cookie);

    (jar, Redirect::temporary(auth_url.as_ref())).into_response()
}

#[derive(Deserialize)]
pub struct CallbackParams {
    pub code: String,
    pub state: String,
}

#[derive(Deserialize)]
struct GithubUser {
    id: i64,
    login: String,
    name: Option<String>,
}

#[derive(Deserialize)]
struct GithubEmail {
    email: String,
    primary: bool,
    verified: bool,
}

/// `GET /api/auth/github/callback` — verify state, exchange the code for a
/// token, fetch the user's primary verified email, find-or-create the user,
/// log them in, redirect to /profile.
pub async fn callback(
    State(state): State<Arc<AppState>>,
    mut auth_session: AuthSess,
    jar: CookieJar,
    Query(params): Query<CallbackParams>,
) -> Response {
    let Some(ref cfg) = state.oauth_github else {
        return oauth_unconfigured();
    };

    // 1. State check.
    let cookie_state = match jar.get(STATE_COOKIE).map(|c| c.value().to_owned()) {
        Some(v) => v,
        None => return bad_request("missing oauth state cookie"),
    };
    if cookie_state != params.state {
        return bad_request("oauth state mismatch");
    }
    // Always clear the cookie after one use.
    let jar = jar.remove(Cookie::from(STATE_COOKIE));

    // 2. Exchange code → token.
    let client = build_client(cfg);
    let token = match client
        .exchange_code(AuthorizationCode::new(params.code))
        .request_async(async_http_client)
        .await
    {
        Ok(t) => t,
        Err(e) => {
            tracing::warn!(error = %e, "github code exchange failed");
            return upstream_error("code_exchange_failed");
        }
    };
    let access_token = token.access_token().secret().clone();

    // 3. Fetch user identity + emails.
    let http = match reqwest::Client::builder().user_agent("nasrudin-api").build() {
        Ok(c) => c,
        Err(e) => {
            tracing::error!(error = %e, "reqwest client build failed");
            return upstream_error("http_client_init_failed");
        }
    };

    let gh_user: GithubUser = match http
        .get("https://api.github.com/user")
        .bearer_auth(&access_token)
        .header(header::ACCEPT, "application/vnd.github+json")
        .send()
        .await
        .and_then(|r| r.error_for_status())
    {
        Ok(r) => match r.json().await {
            Ok(u) => u,
            Err(e) => {
                tracing::warn!(error = %e, "github user json parse failed");
                return upstream_error("user_parse_failed");
            }
        },
        Err(e) => {
            tracing::warn!(error = %e, "github user fetch failed");
            return upstream_error("user_fetch_failed");
        }
    };

    let emails: Vec<GithubEmail> = match http
        .get("https://api.github.com/user/emails")
        .bearer_auth(&access_token)
        .header(header::ACCEPT, "application/vnd.github+json")
        .send()
        .await
        .and_then(|r| r.error_for_status())
    {
        Ok(r) => r.json().await.unwrap_or_default(),
        Err(e) => {
            tracing::warn!(error = %e, "github emails fetch failed");
            return upstream_error("emails_fetch_failed");
        }
    };

    let primary = match emails.iter().find(|e| e.primary && e.verified) {
        Some(p) => p,
        None => return upstream_error("no_verified_primary_email"),
    };

    // 4. Find-or-create.
    let pg = auth_session.backend.db.clone();
    let user_model = match nasrudin_pg::query::users::find_or_create_from_github(
        &pg,
        gh_user.id,
        &gh_user.login,
        &primary.email,
        gh_user.name.as_deref(),
    )
    .await
    {
        Ok(m) => m,
        Err(e) => {
            tracing::warn!(error = %e, "find_or_create_from_github failed");
            return conflict_error("github_link_conflict");
        }
    };

    let auth_user = AuthUser::from_model(user_model);

    // 5. Sign in via axum-login.
    if let Err(e) = auth_session.login(&auth_user).await {
        tracing::error!(error = %e, "axum-login session create failed");
        return upstream_error("session_create_failed");
    }

    // 6. Redirect to /profile.
    (jar, Redirect::temporary("/profile")).into_response()
}

fn bad_request(msg: &str) -> Response {
    (
        StatusCode::BAD_REQUEST,
        Json(serde_json::json!({ "error": msg })),
    )
        .into_response()
}

fn upstream_error(msg: &str) -> Response {
    (
        StatusCode::BAD_GATEWAY,
        Json(serde_json::json!({ "error": msg })),
    )
        .into_response()
}

fn conflict_error(msg: &str) -> Response {
    (
        StatusCode::CONFLICT,
        Json(serde_json::json!({ "error": msg })),
    )
        .into_response()
}
