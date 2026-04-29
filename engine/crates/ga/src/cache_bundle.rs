//! Owned bundle of caches + identity passed into `verify_chain`.
//!
//! Holds `Arc`s rather than borrows so the bundle can sit on
//! `DiscoveryConfig` (which is `Clone`) without lifetime gymnastics.
//! Each verify call clones the bundle (cheap — just refcount bumps).

use std::sync::Arc;

use nasrudin_derive::CacheStats;
use nasrudin_rocks::{AttemptsCache, TacticPriorsCache};

#[derive(Clone)]
pub struct CacheBundle {
    pub attempts: Arc<AttemptsCache>,
    pub tactic_priors: Arc<TacticPriorsCache>,
    pub stats: Arc<CacheStats>,
    /// E.g. `"4.27.0"`. Used as `AttemptRecord.lean_version`.
    pub lean_version: String,
    /// E.g. `"worker-abcd"`. Used as `AttemptRecord.attempted_by`.
    pub worker_id: String,
    /// 30 in production. Tests pass a low value (or `i64::MAX` for "never expire").
    pub ttl_days: i64,
}

impl std::fmt::Debug for CacheBundle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The two RocksDB caches don't impl Debug; surface the fields
        // we *can* show. `DiscoveryConfig` derives Debug, so this lets
        // the GA's debug logging print a meaningful summary.
        f.debug_struct("CacheBundle")
            .field("lean_version", &self.lean_version)
            .field("worker_id", &self.worker_id)
            .field("ttl_days", &self.ttl_days)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn bundle_can_be_constructed_and_cloned() {
        let dir_a = tempdir().unwrap();
        let attempts = Arc::new(AttemptsCache::open(dir_a.path().to_str().unwrap()).unwrap());
        let dir_t = tempdir().unwrap();
        let priors = Arc::new(TacticPriorsCache::open(dir_t.path().to_str().unwrap()).unwrap());
        let bundle = CacheBundle {
            attempts,
            tactic_priors: priors,
            stats: Arc::new(CacheStats::default()),
            lean_version: "4.27.0".into(),
            worker_id: "test".into(),
            ttl_days: 30,
        };
        let _cloned = bundle.clone();
        assert_eq!(bundle.lean_version, "4.27.0");
        assert_eq!(bundle.ttl_days, 30);
    }
}
