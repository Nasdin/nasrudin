//! Server-side cache wiring.
//!
//! Owns the long-lived `AttemptsCache` and `TacticPriorsCache` against
//! the engine's main `TheoremDb`, plus the `CacheStats` counter sink.
//! Constructed once in `main.rs` from `CacheConfig::from_env()` and
//! plumbed into `AppState` and `ReverifyQueue`.

use std::sync::Arc;

use nasrudin_derive::{CacheConfig, CacheStats};
use nasrudin_ga::CacheBundle;
use nasrudin_rocks::{AttemptsCache, TacticPriorsCache, TheoremDb};

/// Long-lived cache state held on `AppState`. `config` is read at
/// boot and stored alongside the bundle so callers can inspect
/// individual flags (`config.attempts_enabled`, etc.) without
/// re-reading env each call.
pub struct CacheCtx {
    pub config: CacheConfig,
    pub bundle: CacheBundle,
}

impl CacheCtx {
    /// Build from `CacheConfig::from_env()` against the engine's main
    /// `TheoremDb`. Caches are constructed unconditionally — the
    /// per-flag gating happens at the call site (we still pay the
    /// `Arc<DB>` clone, which is one atomic-increment).
    ///
    /// `lean_version` and `worker_id` are stamped onto every cached
    /// `AttemptRecord`. Read from env (`NASRUDIN_LEAN_VERSION`,
    /// `NASRUDIN_WORKER_ID`) with sensible defaults.
    pub fn build(db: &Arc<TheoremDb>) -> anyhow::Result<Self> {
        let config = CacheConfig::from_env();
        let attempts = Arc::new(AttemptsCache::on_existing_db(db.shared_db())?);
        let tactic_priors = Arc::new(TacticPriorsCache::on_existing_db(db.shared_db())?);
        let stats = Arc::new(CacheStats::default());
        let lean_version =
            std::env::var("NASRUDIN_LEAN_VERSION").unwrap_or_else(|_| "4.27.0".into());
        let worker_id =
            std::env::var("NASRUDIN_WORKER_ID").unwrap_or_else(|_| "api-server".into());
        let bundle = CacheBundle {
            attempts,
            tactic_priors,
            stats,
            lean_version,
            worker_id,
            ttl_days: 30,
        };
        Ok(Self { config, bundle })
    }
}
