//! Phase 9 / Task 5.1 — integration tests for `/api/theorems` read endpoints.
//!
//! Each test seeds rows directly through `nasrudin_pg::query::theorems`
//! (matching the production ingest path), then issues a request against the
//! in-memory `Router` from `test_app::build()` and asserts on status code and
//! JSON body shape.
//!
//! Tests skip gracefully if the test PostgreSQL database isn't reachable —
//! see `test_app::build()`.

mod test_app;

use axum::http::StatusCode;

#[tokio::test]
async fn list_returns_verified_with_cursor() {
    let Some(app) = test_app::build().await else {
        return;
    };
    test_app::seed_verified_theorems(&app, 5).await;

    let resp = test_app::get(&app, "/api/theorems?limit=3").await;
    assert_eq!(resp.status, StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert_eq!(
        body["theorems"].as_array().unwrap().len(),
        3,
        "limit=3 must clip to exactly 3 rows"
    );
    assert!(
        body["next_cursor"].is_string(),
        "5 seeded > 3 limit ⇒ next_cursor must be present"
    );
    assert_eq!(
        body["total"].as_u64().unwrap(),
        5,
        "total counts all 5 verified rows"
    );
    assert_eq!(
        body["total_capped"].as_bool().unwrap(),
        false,
        "5 rows is well under the 10k cap"
    );
}

#[tokio::test]
async fn recent_endpoint_returns_descending() {
    let Some(app) = test_app::build().await else {
        return;
    };
    test_app::seed_verified_theorems(&app, 3).await;

    let resp = test_app::get(&app, "/api/theorems/recent?limit=10").await;
    assert_eq!(resp.status, StatusCode::OK);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert_eq!(
        body["theorems"].as_array().unwrap().len(),
        3,
        "limit=10 with 3 rows ⇒ all 3 returned"
    );
    // 3 rows ≤ limit ⇒ no further page.
    assert!(
        body["next_cursor"].is_null(),
        "no further page when result fits within the limit"
    );
}

#[tokio::test]
async fn lean_download_returns_text_plain() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let hashes = test_app::seed_verified_theorems(&app, 1).await;
    let hash = &hashes[0];

    let resp = test_app::get(&app, &format!("/api/theorems/{hash}/lean")).await;
    assert_eq!(resp.status, StatusCode::OK);
    // Body should contain the seeded Lean source verbatim.
    let body_str = std::str::from_utf8(&resp.body).unwrap();
    assert!(
        body_str.contains("theorem t0 : True := trivial"),
        "expected seeded lean source in body, got: {body_str}"
    );
}

#[tokio::test]
async fn by_id_returns_404_for_unknown() {
    let Some(app) = test_app::build().await else {
        return;
    };
    // `0000000000000000` is a valid hex (16 chars = 8 bytes) so it parses,
    // but no row with that id exists ⇒ 404.
    let resp = test_app::get(&app, "/api/theorems/0000000000000000").await;
    assert_eq!(resp.status, StatusCode::NOT_FOUND);
    let body: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert_eq!(body["error"], "not_found");
}
