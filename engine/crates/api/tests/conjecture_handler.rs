//! Smoke tests for `/api/conjecture` (Phase D).
//!
//! Mirrors `llm_keys_handler.rs`: each route is exercised without auth
//! to verify the gate fires (401 across the board). Behavioural coverage
//! is split across:
//!   * `nasrudin_llm`'s wiremock provider tests (LLM contract)
//!   * the `conjecture::types` and `conjecture::prompt` unit tests
//!   * the future `e2e_conjecture_emc2` nightly (full loop)

mod test_app;

use axum::body::{to_bytes, Body};
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

const ZERO_UUID: &str = "00000000-0000-0000-0000-000000000000";

#[tokio::test]
async fn create_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let body = serde_json::json!({
        "hunch": "Energy and mass relate via c²",
        "provider": "anthropic",
        "model": "claude-sonnet-4-6",
        "budget": {"wall_seconds": 60, "max_candidates": 100},
    });
    let resp = test_app::post(&app, "/api/conjecture", &body, None).await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn start_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let body = serde_json::json!({"chosen_index": 0});
    let resp = test_app::post(
        &app,
        &format!("/api/conjecture/{ZERO_UUID}/start"),
        &body,
        None,
    )
    .await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn get_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, &format!("/api/conjecture/{ZERO_UUID}")).await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn sse_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let req = Request::builder()
        .method("GET")
        .uri(format!("/api/conjecture/{ZERO_UUID}/sse"))
        .body(Body::empty())
        .unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let _ = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn list_mine_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, "/api/me/conjectures").await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}
