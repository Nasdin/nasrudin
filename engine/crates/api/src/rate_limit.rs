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
