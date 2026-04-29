//! Smoke test for `/api/me/llm-keys` (Phase C).
//!
//! End-to-end authenticated coverage requires standing up a session
//! cookie or a `nsk_live_…` API key, which the rest of the test
//! harness doesn't plumb through yet (see me_stats.rs for the same
//! pattern). Asserting the 401 path on each verb is sufficient to
//! prove the routes are wired and the auth gate is in front of them.
//!
//! The wiremock-based provider tests in `engine/crates/llm/tests/` and
//! the encryption unit tests in `nasrudin_llm::encryption::tests`
//! cover the behavioural surface this handler delegates to.

mod test_app;

use axum::body::{to_bytes, Body};
use axum::http::Request;
use axum::http::StatusCode;
use tower::ServiceExt;

#[tokio::test]
async fn unauthenticated_get_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, "/api/me/llm-keys").await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn unauthenticated_post_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let body = serde_json::json!({"provider": "anthropic", "key": "sk-…"});
    let resp = test_app::post(&app, "/api/me/llm-keys", &body, None).await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn unauthenticated_delete_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let req = Request::builder()
        .method("DELETE")
        .uri("/api/me/llm-keys/anthropic")
        .body(Body::empty())
        .unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let _ = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}
