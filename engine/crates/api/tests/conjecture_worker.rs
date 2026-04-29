//! Smoke tests for Phase E worker endpoints. Validates:
//!   - All four routes are mounted
//!   - Unauthenticated requests get 401
//! Behavioural coverage of the dequeue/heartbeat/submit/complete cycle is
//! handled by the pg-integration tests (`conjecture_jobs_query`).

mod test_app;

use axum::body::{to_bytes, Body};
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

const ZERO_UUID: &str = "00000000-0000-0000-0000-000000000000";

async fn post_unauth(app: &test_app::TestApp, path: &str, body: &serde_json::Value) -> StatusCode {
    let req = Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", "application/json")
        .body(Body::from(serde_json::to_vec(body).unwrap()))
        .unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let _ = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    status
}

#[tokio::test]
async fn claim_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let status = post_unauth(&app, "/api/conjecture/claim", &serde_json::json!({})).await;
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn heartbeat_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let status = post_unauth(
        &app,
        &format!("/api/conjecture/{ZERO_UUID}/heartbeat"),
        &serde_json::json!({"candidates_attempted":0,"candidates_verified":0,"time_elapsed_s":0}),
    )
    .await;
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn submit_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let status = post_unauth(
        &app,
        &format!("/api/conjecture/{ZERO_UUID}/submit"),
        &serde_json::json!({
            "engine_git_sha":"sha","lean_version":"v","theorem":{
                "canonical_statement":"x","domain":"PureMath",
                "lean_source":"theorem x : True := trivial","chain":[],"axioms_used":[]
            }
        }),
    )
    .await;
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn complete_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let status = post_unauth(
        &app,
        &format!("/api/conjecture/{ZERO_UUID}/complete"),
        &serde_json::json!({"outcome":"NoResult"}),
    )
    .await;
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}
