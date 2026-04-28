//! Phase 9 / Task 6.1 — `GET /api/workers` + `POST /api/workers/heartbeat`.
//!
//! Two focused integration tests:
//!
//! 1. `list_endpoint_returns_workers_array`: the public list endpoint serves a
//!    JSON array (not an envelope object) ordered by `theorems_contributed`.
//!    The harness seeds one row, so the array is non-empty.
//! 2. `heartbeat_without_bearer_returns_401`: the heartbeat extractor rejects
//!    unauthenticated requests before any DB lookup runs.
//!
//! The full happy-path heartbeat (with a real `nsk_worker_` Argon2-hashed
//! token) is exercised by the higher-level ingest flow tests, which already
//! depend on the full live database.

mod test_app;

use axum::http::StatusCode;

#[tokio::test]
async fn list_endpoint_returns_workers_array() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, "/api/workers").await;
    assert_eq!(resp.status, StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert!(body.is_array(), "expected array body, got {body}");
    // Harness seeds a single "test-worker" row.
    let arr = body.as_array().unwrap();
    assert!(
        arr.iter().any(|v| v.get("id").and_then(|s| s.as_str()) == Some("test-worker")),
        "expected seeded test-worker in list, got {body}"
    );
}

#[tokio::test]
async fn heartbeat_without_bearer_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::post(
        &app,
        "/api/workers/heartbeat",
        &serde_json::json!({
            "worker_id": "test-worker",
            "current_generation": 17,
            "theorems_produced_total": 100,
            "uptime_seconds": 60,
            "engine_git_sha": "deadbee"
        }),
        None,
    )
    .await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}
