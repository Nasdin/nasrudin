//! Integration tests for `GET /api/stats/landing`.
//! Skips when the test database is unreachable.

mod test_app;

#[tokio::test]
async fn landing_returns_expected_shape() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let resp = test_app::get(&app, "/api/stats/landing").await;
    assert_eq!(resp.status, 200);

    let v: serde_json::Value = serde_json::from_slice(&resp.body).expect("valid JSON");
    assert!(
        v.get("verified_theorems")
            .and_then(|n| n.as_u64())
            .is_some()
    );
    assert!(v.get("active_workers").and_then(|n| n.as_u64()).is_some());
    assert!(v.get("contributors").and_then(|n| n.as_u64()).is_some());

    // Test harness seeds one worker via register() → it's still active and
    // counted as one of the live workers, but it has no api_keys row, so
    // the contributor count is 0.
    assert_eq!(v.get("active_workers").unwrap().as_u64().unwrap(), 1);
    assert_eq!(v.get("contributors").unwrap().as_u64().unwrap(), 0);
    assert_eq!(v.get("verified_theorems").unwrap().as_u64().unwrap(), 0);
}

#[tokio::test]
async fn landing_cache_returns_same_bytes_within_ttl() {
    let Some(app) = test_app::build().await else {
        return;
    };
    let one = test_app::get(&app, "/api/stats/landing").await;
    let two = test_app::get(&app, "/api/stats/landing").await;
    assert_eq!(one.status, 200);
    assert_eq!(two.status, 200);
    assert_eq!(
        one.body, two.body,
        "second call within 60s must be a cache hit"
    );
}
