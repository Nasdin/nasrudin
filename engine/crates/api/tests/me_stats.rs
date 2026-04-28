//! Smoke test for `GET /api/me/stats` (Phase 9 Task 6.2).
//!
//! End-to-end authenticated coverage requires standing up a session cookie
//! or a `nsk_live_…` API key, which the rest of the test harness doesn't
//! plumb through yet. Asserting the 401 path is sufficient to prove the
//! route is wired and the auth gate is in front of it.

mod test_app;

use axum::http::StatusCode;

#[tokio::test]
async fn unauthenticated_returns_401() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, "/api/me/stats").await;
    assert_eq!(resp.status, StatusCode::UNAUTHORIZED);
}
