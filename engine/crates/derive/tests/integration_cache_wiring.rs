//! End-to-end: feed a synthetic verifier outcome through the cache,
//! then call again with the same key and confirm the verifier is NOT
//! invoked the second time. This is the regression net for "the GA
//! actually skips lake build on a known-rejected canonical".

use chrono::{Duration, Utc};
use nasrudin_derive::lean_verify::{
    LeanVerifier, LeanVerifyResult, VerifyWithCacheCtx, verify_with_cache,
};
use nasrudin_rocks::{AttemptOutcome, AttemptRecord, AttemptsCache};
use tempfile::tempdir;

#[test]
fn second_call_with_same_key_short_circuits_via_cache() {
    let dir_cache = tempdir().unwrap();
    let cache = AttemptsCache::open(dir_cache.path().to_str().unwrap()).unwrap();
    let cache_key = [0xab; 16];

    cache
        .put(
            &cache_key,
            &AttemptRecord {
                outcome: AttemptOutcome::Verified {
                    theorem_id: [0u8; 8],
                    tactic: "decide".into(),
                },
                lean_version: "4.27.0".into(),
                timestamp: Utc::now(),
                attempted_by: "fixture".into(),
                elapsed_ms: 1,
            },
        )
        .unwrap();

    // LeanVerifier pointing at /nonexistent: a real verify_file would
    // ProcessError. Cache hit must short-circuit before that, so we
    // expect Success.
    let verifier = LeanVerifier::new("/nonexistent");
    let ctx = VerifyWithCacheCtx {
        verifier: &verifier,
        cache: &cache,
        cache_key: &cache_key,
        lean_version: "4.27.0",
        worker_id: "test",
        ttl_days: 30,
    };
    let result = verify_with_cache(&ctx, "stub source", "Stub.Module");
    assert!(
        matches!(result, LeanVerifyResult::Success),
        "expected Success from cache hit, got {:?}",
        result
    );
}

#[test]
fn miss_then_hit_short_circuits_after_first_compute() {
    let dir = tempdir().unwrap();
    let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
    let key = [0xcd; 16];
    let mut compute_calls = 0;
    let max_age = Duration::days(30);

    let _r1 = cache
        .lookup_or_compute(&key, max_age, "w1", "4.27.0", || {
            compute_calls += 1;
            AttemptOutcome::RejectedTimeout
        })
        .unwrap();

    let _r2 = cache
        .lookup_or_compute(&key, max_age, "w1", "4.27.0", || {
            compute_calls += 1;
            AttemptOutcome::RejectedTimeout
        })
        .unwrap();

    assert_eq!(compute_calls, 1, "second call should hit cache");
}

#[test]
fn cache_skips_persistence_on_process_error() {
    let dir = tempdir().unwrap();
    let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
    let key = [0xef; 16];

    let verifier = LeanVerifier::new("/nonexistent");
    let ctx = VerifyWithCacheCtx {
        verifier: &verifier,
        cache: &cache,
        cache_key: &key,
        lean_version: "4.27.0",
        worker_id: "test",
        ttl_days: 30,
    };
    let _ = verify_with_cache(&ctx, "stub source", "Stub.Module");

    assert!(
        cache.get(&key).unwrap().is_none(),
        "ProcessError must not be cached"
    );
}
