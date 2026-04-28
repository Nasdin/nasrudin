//! Integration tests for `GET /api/seed` (Phase 9 Task 5.3).
//!
//! Validates the remote-worker bootstrap shape: `{axioms, seed_theorems}`,
//! the `top` cap, and that the `domain=…` filter is accepted.

mod test_app;

use axum::http::StatusCode;

#[tokio::test]
async fn seed_returns_axioms_and_seed_theorems() {
    let Some(app) = test_app::build().await else {
        return;
    };
    test_app::seed_verified_theorems(&app, 5).await;
    let resp = test_app::get(&app, "/api/seed?top=3").await;
    assert_eq!(resp.status, StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert!(body["axioms"].is_array(), "axioms field must be an array");
    assert!(
        body["seed_theorems"].is_array(),
        "seed_theorems field must be an array"
    );
    assert!(body["seed_theorems"].as_array().unwrap().len() <= 3);
}

#[tokio::test]
async fn seed_with_domain_filter() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, "/api/seed?domain=PureMath&top=5").await;
    assert_eq!(resp.status, StatusCode::OK);
}
