//! Per-route-group rate limiting via tower_governor (GCRA algorithm).
//!
//! Each function returns a shared `GovernorConfig` keyed by peer IP.
//! Attach via `GovernorLayer::new(config)` on the appropriate sub-router.

use std::time::Duration;

use governor::middleware::NoOpMiddleware;
use tower_governor::governor::GovernorConfig;
use tower_governor::governor::GovernorConfigBuilder;
use tower_governor::key_extractor::PeerIpKeyExtractor;

/// Concrete config type: per-IP keying, no extra middleware.
pub type IpGovConfig = GovernorConfig<PeerIpKeyExtractor, NoOpMiddleware>;

/// Auth-strict: brute-force protection for login/register.
/// 5 req/min sustained, burst 5.
pub fn auth_strict() -> IpGovConfig {
    GovernorConfigBuilder::default()
        .period(Duration::from_secs(12)) // 1 token per 12s → 5/min
        .burst_size(5)
        .finish()
        .expect("valid auth_strict governor config")
}

/// Auth-session: lightweight session ops (logout, me).
/// 30 req/min sustained, burst 10.
pub fn auth_session() -> IpGovConfig {
    GovernorConfigBuilder::default()
        .per_second(2) // ~30/min replenish
        .burst_size(10)
        .finish()
        .expect("valid auth_session governor config")
}

/// API-standard: core read API (theorems, domains, search, GA status).
/// 60 req/min sustained, burst 20.
pub fn api_standard() -> IpGovConfig {
    GovernorConfigBuilder::default()
        .per_second(1) // 60/min replenish
        .burst_size(20)
        .finish()
        .expect("valid api_standard governor config")
}

/// Health-relaxed: monitoring & liveness endpoints.
/// 120 req/min sustained, burst 30.
pub fn health_relaxed() -> IpGovConfig {
    GovernorConfigBuilder::default()
        .per_millisecond(500) // 2/sec → 120/min replenish
        .burst_size(30)
        .finish()
        .expect("valid health_relaxed governor config")
}

/// Platform-user: 60 req/min sustained, burst 30.
pub fn platform_user() -> IpGovConfig {
    GovernorConfigBuilder::default()
        .per_second(1) // 60/min replenish
        .burst_size(30)
        .finish()
        .expect("valid platform_user governor config")
}

/// Platform-worker: 300 req/min sustained, burst 120.
pub fn platform_worker() -> IpGovConfig {
    GovernorConfigBuilder::default()
        .per_millisecond(200) // 5/sec → 300/min replenish
        .burst_size(120)
        .finish()
        .expect("valid platform_worker governor config")
}

// ---------------------------------------------------------------------------
// WorkerRateLimiter — keyed by worker_id (string), used by /api/ingest.
// ---------------------------------------------------------------------------

use governor::{
    Quota, RateLimiter,
    clock::{DefaultClock, QuantaInstant},
    state::keyed::DefaultKeyedStateStore,
};
use std::num::NonZeroU32;
use std::sync::Arc;

/// Per-worker token-bucket rate limiter keyed by `worker_id` (string).
///
/// Default 60 requests/minute. Used by `/api/ingest` (Phase 9 Task 4.2) to
/// throttle individual workers independently of the per-IP `tower_governor`
/// layer that fronts the public router.
pub struct WorkerRateLimiter {
    inner: Arc<RateLimiter<String, DefaultKeyedStateStore<String>, DefaultClock>>,
}

impl WorkerRateLimiter {
    /// Build a new limiter that allows `per_minute` requests/min per worker.
    /// Values < 1 are clamped to 1 (governor requires a non-zero quota).
    pub fn new(per_minute: u32) -> Self {
        let quota = Quota::per_minute(NonZeroU32::new(per_minute.max(1)).unwrap());
        Self {
            inner: Arc::new(RateLimiter::keyed(quota)),
        }
    }

    /// Try to consume `n` tokens for `worker_id`. Returns `Ok(())` if all
    /// `n` tokens were available, `Err(NotUntil)` describing when the next
    /// token will be available if the bucket was exhausted partway through.
    /// The handler maps `Err` to HTTP 429.
    ///
    /// `governor` doesn't expose a "consume N atomically" API — we call
    /// `check_key` once per token. For batch ingest with N theorems this
    /// means N independent token checks. Behaviour is correct (1 batch of N
    /// = N tokens) and the `QuantaClock` keeps it cheap.
    pub fn check_and_consume(
        &self,
        worker_id: &str,
        n: u32,
    ) -> Result<(), governor::NotUntil<QuantaInstant>> {
        let key = worker_id.to_string();
        for _ in 0..n.max(1) {
            self.inner.check_key(&key)?;
        }
        Ok(())
    }
}
