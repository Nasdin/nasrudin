//! Property-based tests for trust sampling. The hash-mod trick is
//! supposed to be:
//! - deterministic (same input → same output, so a re-run picks the
//!   same sampled subset)
//! - never-promote when trusted+rate=0
//! - always-promote when trusted+rate=1 OR untrusted
//! - approximately-uniform 1-in-N for trusted+rate=N

use physics_api::trust::{TrustDecision, TrustSource, should_promote};
use proptest::prelude::*;

fn dec(trusted: bool, rate: u32) -> TrustDecision {
    TrustDecision {
        trusted,
        spot_check_rate: rate,
        source: if trusted {
            TrustSource::UserFlag
        } else {
            TrustSource::Default
        },
    }
}

proptest! {
    #[test]
    fn determinism(rate in 1u32..200, id in any::<[u8; 8]>()) {
        let d = dec(true, rate);
        prop_assert_eq!(should_promote(&d, &id), should_promote(&d, &id));
    }

    #[test]
    fn untrusted_always_promotes(rate in 0u32..200, id in any::<[u8; 8]>()) {
        let d = dec(false, rate);
        prop_assert!(should_promote(&d, &id));
    }
}

#[test]
fn trusted_rate_zero_never_promotes() {
    let d = dec(true, 0);
    for i in 0..1000_u64 {
        assert!(!should_promote(&d, &i.to_le_bytes()));
    }
}

#[test]
fn trusted_rate_one_always_promotes() {
    let d = dec(true, 1);
    for i in 0..1000_u64 {
        assert!(should_promote(&d, &i.to_le_bytes()));
    }
}

#[test]
fn sampling_uniformity_50_within_20pct() {
    // 10k samples at rate=50 should produce ≈200 promotions. Allow ±20%
    // (i.e., 160..=240) — this is FNV-1a, not cryptographic, but it's
    // good enough that the empirical ratio tracks the expected one
    // closely. Tightening below ±20% risks flakes from a single bad
    // distribution; ±20% catches "obvious" miscalibration.
    let d = dec(true, 50);
    let mut promoted = 0_usize;
    for i in 0..10_000_u64 {
        if should_promote(&d, &i.to_le_bytes()) {
            promoted += 1;
        }
    }
    let expected = 10_000 / 50;
    let lo = expected * 80 / 100;
    let hi = expected * 120 / 100;
    assert!(
        (lo..=hi).contains(&promoted),
        "promoted={promoted} expected≈{expected}",
    );
}

#[test]
fn sampling_uniformity_100_within_25pct() {
    // Smaller expected value (~100), so wider tolerance.
    let d = dec(true, 100);
    let mut promoted = 0_usize;
    for i in 0..10_000_u64 {
        if should_promote(&d, &i.to_le_bytes()) {
            promoted += 1;
        }
    }
    let expected = 10_000 / 100;
    let lo = expected * 75 / 100;
    let hi = expected * 125 / 100;
    assert!(
        (lo..=hi).contains(&promoted),
        "promoted={promoted} expected≈{expected}",
    );
}
