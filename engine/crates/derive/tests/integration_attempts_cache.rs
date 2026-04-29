//! End-to-end attempts-cache integration test:
//! 1000 cache writes, mixed hits/misses, verify counts and TTL semantics
//! hold under repeated access.

use chrono::{Duration, Utc};
use nasrudin_rocks::attempts_cache::{AttemptOutcome, AttemptRecord, AttemptsCache};
use tempfile::tempdir;

#[test]
fn attempts_cache_handles_thousand_inserts() {
    let dir = tempdir().unwrap();
    let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();

    let mut hits = 0u32;
    let mut misses = 0u32;
    let max_age = Duration::days(30);

    for i in 0u32..1_000 {
        let mut key = [0u8; 16];
        key[..4].copy_from_slice(&i.to_be_bytes());
        // First lookup — miss.
        if cache.get_with_ttl(&key, max_age).unwrap().is_some() {
            hits += 1;
        } else {
            misses += 1;
        }
        // Insert.
        let rec = AttemptRecord {
            outcome: if i % 7 == 0 {
                AttemptOutcome::Verified {
                    theorem_id: [0; 8],
                    tactic: "ring".into(),
                }
            } else {
                AttemptOutcome::RejectedTimeout
            },
            lean_version: "4.27.0".into(),
            timestamp: Utc::now(),
            attempted_by: "soak".into(),
            elapsed_ms: 1,
        };
        cache.put(&key, &rec).unwrap();
    }
    assert_eq!(misses, 1000);
    assert_eq!(hits, 0);

    // Second pass — every key now hits.
    let mut second_hits = 0u32;
    for i in 0u32..1_000 {
        let mut key = [0u8; 16];
        key[..4].copy_from_slice(&i.to_be_bytes());
        if cache.get_with_ttl(&key, max_age).unwrap().is_some() {
            second_hits += 1;
        }
    }
    assert_eq!(second_hits, 1000);
}
