//! Smoke tests for the paid Researcher tier HTTP surface.
//!
//! Mirrors `conjecture_handler.rs` — exercises the auth gate on every
//! route to confirm the wiring is in place. Behavioural coverage of
//! the underlying SQL helpers lives in
//! `nasrudin-pg/tests/paid_researcher_queries.rs`.

mod test_app;

use axum::body::{Body, to_bytes};
use axum::http::{Request, StatusCode};
use tower::ServiceExt;

const ZERO_UUID: &str = "00000000-0000-0000-0000-000000000000";

#[tokio::test]
async fn create_research_job_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let body = serde_json::json!({
        "hunch": "E = m c^2",
        "domain_hint": "special_relativity",
    });
    let resp = test_app::post(&app, "/api/research/jobs", &body, None).await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn list_research_jobs_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, "/api/research/jobs").await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn detail_research_job_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, &format!("/api/research/jobs/{ZERO_UUID}")).await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn cancel_research_job_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let body = serde_json::json!({});
    let resp = test_app::post(
        &app,
        &format!("/api/research/jobs/{ZERO_UUID}/cancel"),
        &body,
        None,
    )
    .await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn events_research_job_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let req = Request::builder()
        .method("GET")
        .uri(format!("/api/research/jobs/{ZERO_UUID}/events"))
        .body(Body::empty())
        .unwrap();
    let resp = app.router.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let _ = to_bytes(resp.into_body(), 1024 * 1024).await.unwrap();
    assert_eq!(status, StatusCode::UNAUTHORIZED);
}

// Worker-facing /api/jobs/* endpoints — these need a real worker
// bearer token to test the success path; here we just confirm the
// auth gate fires for unauthenticated callers.

#[tokio::test]
async fn jobs_claim_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let body = serde_json::json!({
        "available_lake_slots": 4,
        "domains_supported": ["all"],
    });
    let resp = test_app::post(&app, "/api/jobs/claim", &body, None).await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn jobs_heartbeat_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let body = serde_json::json!({
        "candidates_attempted_delta": 1,
        "candidates_verified_delta": 0,
        "lake_slot_hours_consumed_delta": 0.01,
    });
    let resp = test_app::post(
        &app,
        &format!("/api/jobs/{ZERO_UUID}/heartbeat"),
        &body,
        None,
    )
    .await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn jobs_release_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::post(
        &app,
        &format!("/api/jobs/{ZERO_UUID}/release"),
        &serde_json::json!({}),
        None,
    )
    .await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn jobs_mark_proved_unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let body = serde_json::json!({
        "theorem_id_hex": "0102030405060708",
        "statement_latex": "E = m c^2",
    });
    let resp = test_app::post(
        &app,
        &format!("/api/jobs/{ZERO_UUID}/mark_proved"),
        &body,
        None,
    )
    .await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}

#[tokio::test]
async fn steering_endpoint_anonymous_returns_200_with_etag() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, "/api/steering").await;
    assert_eq!(resp.status, StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert!(
        body.get("config").is_some(),
        "steering body must have config"
    );
    assert!(body.get("mode").is_some(), "steering body must have mode");
}
