//! Phase 9 Task 4.1 — per-worker token-bucket limiter (`WorkerRateLimiter`).
//!
//! Verifies that the limiter:
//!   1. Allows the burst-capacity worth of requests then throttles further ones.
//!   2. Maintains independent buckets per worker_id key.
//!   3. Consumes exactly `n` tokens on a batch call.

use physics_api::rate_limit::WorkerRateLimiter;

#[test]
fn allows_burst_then_throttles() {
    let lim = WorkerRateLimiter::new(60);
    // First 60 calls (burst capacity = quota for governor's token bucket) succeed.
    let mut allowed = 0;
    for _ in 0..60 {
        if lim.check_and_consume("w1", 1).is_ok() {
            allowed += 1;
        }
    }
    assert_eq!(allowed, 60, "first 60 should pass");
    assert!(
        lim.check_and_consume("w1", 1).is_err(),
        "61st should be rate-limited"
    );
}

#[test]
fn separate_keys_have_separate_buckets() {
    let lim = WorkerRateLimiter::new(60);
    for _ in 0..60 {
        let _ = lim.check_and_consume("w1", 1);
    }
    assert!(lim.check_and_consume("w1", 1).is_err());
    assert!(
        lim.check_and_consume("w2", 1).is_ok(),
        "different worker has independent bucket"
    );
}

#[test]
fn batch_n_consumes_n_tokens() {
    let lim = WorkerRateLimiter::new(60);
    assert!(lim.check_and_consume("w1", 30).is_ok());
    assert!(lim.check_and_consume("w1", 30).is_ok());
    // 60 total consumed; next one fails.
    assert!(lim.check_and_consume("w1", 1).is_err());
}
