//! RocksDB-backed cache of which tactic chains have proven goals of a given
//! shape (skeleton hash).
//!
//! ## Key
//!
//! 16 bytes: `(skeleton_hash || axiom_set_hash)`.
//! - `skeleton_hash` (8 bytes) — `nasrudin_core::skeleton::skeleton_hash` of
//!   the goal expression.
//! - `axiom_set_hash` (8 bytes) — BLAKE3 over the sorted axiom IDs in scope.
//!
//! ## Value
//!
//! `serde_json`-encoded [`TacticPriorRecord`]: a list of past tactic-chain
//! successes with hit counts and rolling-average elapsed times. Sorted by
//! hit count desc on read (via [`TacticPriorsCache::top`]).
//!
//! ## Lifetime
//!
//! No TTL. Tactic priors only get better over time; the working set is
//! bounded by the number of distinct goal skeletons (~10⁵ in steady state).

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use rocksdb::DB;
use serde::{Deserialize, Serialize};

const CF_TACTIC_PRIORS: &str = "tactic_priors";

/// One past success record: a tactic chain that proved a goal of the
/// shape this row covers, and how often / how fast.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TacticSuccess {
    pub tactic_chain: String,
    pub hits: u32,
    pub avg_elapsed_ms: u16,
}

/// Per-skeleton record. The list is unsorted on disk; callers use
/// [`TacticPriorsCache::top`] to get a hit-count-sorted subset.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TacticPriorRecord {
    pub successes: Vec<TacticSuccess>,
    pub last_updated: Option<DateTime<Utc>>,
}

/// RocksDB wrapper for the `tactic_priors` column family.
pub struct TacticPriorsCache {
    db: DB,
}

impl TacticPriorsCache {
    /// Open a standalone RocksDB at `path` containing only the
    /// `tactic_priors` CF. (Production reuses the engine's main DB; that
    /// integration is in Phase A.5.)
    pub fn open(path: &str) -> Result<Self> {
        use rocksdb::{ColumnFamilyDescriptor, Options};
        let mut opts = Options::default();
        opts.create_if_missing(true);
        opts.create_missing_column_families(true);
        let cf = ColumnFamilyDescriptor::new(CF_TACTIC_PRIORS, Options::default());
        let db = DB::open_cf_descriptors(&opts, path, vec![cf])
            .context("open tactic_priors db")?;
        Ok(Self { db })
    }

    /// Concatenate the two 8-byte hashes into the 16-byte key.
    pub fn make_key(skeleton_hash: &[u8; 8], axiom_set_hash: &[u8; 8]) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(skeleton_hash);
        out[8..].copy_from_slice(axiom_set_hash);
        out
    }

    /// Get the raw record at `key`. Returns `None` on cache miss.
    pub fn get(&self, key: &[u8; 16]) -> Result<Option<TacticPriorRecord>> {
        let cf = self
            .db
            .cf_handle(CF_TACTIC_PRIORS)
            .context("cf tactic_priors")?;
        match self.db.get_cf(&cf, key).context("get tactic_priors")? {
            Some(bytes) => Ok(Some(
                serde_json::from_slice(&bytes).context("deserialise TacticPriorRecord")?,
            )),
            None => Ok(None),
        }
    }

    /// Top `n` tactic chains for this skeleton, sorted by hit count
    /// descending (ties broken by lexicographic chain string for
    /// determinism).
    pub fn top(&self, key: &[u8; 16], n: usize) -> Result<Vec<TacticSuccess>> {
        let mut rec = self.get(key)?.unwrap_or_default();
        rec.successes
            .sort_by(|a, b| b.hits.cmp(&a.hits).then(a.tactic_chain.cmp(&b.tactic_chain)));
        rec.successes.truncate(n);
        Ok(rec.successes)
    }

    /// Increment hit count for `chain` (or insert), update rolling
    /// average of elapsed time, and stamp `last_updated`.
    pub fn record_success(
        &self,
        key: &[u8; 16],
        chain: &str,
        elapsed_ms: u16,
    ) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_TACTIC_PRIORS)
            .context("cf tactic_priors")?;
        let mut rec = self.get(key)?.unwrap_or_default();
        if let Some(existing) = rec.successes.iter_mut().find(|s| s.tactic_chain == chain) {
            // Rolling average: avg' = ((avg * n) + new) / (n + 1)
            let new_total =
                u32::from(existing.avg_elapsed_ms) * existing.hits + u32::from(elapsed_ms);
            existing.hits += 1;
            existing.avg_elapsed_ms = u16::try_from(new_total / existing.hits).unwrap_or(u16::MAX);
        } else {
            rec.successes.push(TacticSuccess {
                tactic_chain: chain.to_string(),
                hits: 1,
                avg_elapsed_ms: elapsed_ms,
            });
        }
        rec.last_updated = Some(Utc::now());
        let bytes = serde_json::to_vec(&rec).context("serialise TacticPriorRecord")?;
        self.db.put_cf(&cf, key, bytes).context("put tactic_priors")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    fn fresh_cache() -> (TacticPriorsCache, tempfile::TempDir) {
        let dir = tempdir().unwrap();
        (
            TacticPriorsCache::open(dir.path().to_str().unwrap()).unwrap(),
            dir,
        )
    }

    #[test]
    fn record_success_adds_new_entry() {
        let (cache, _dir) = fresh_cache();
        let key = [0xa1; 16];
        cache.record_success(&key, "ring", 12).unwrap();
        let rec = cache.get(&key).unwrap().unwrap();
        assert_eq!(rec.successes.len(), 1);
        assert_eq!(rec.successes[0].tactic_chain, "ring");
        assert_eq!(rec.successes[0].hits, 1);
        assert_eq!(rec.successes[0].avg_elapsed_ms, 12);
        assert!(rec.last_updated.is_some());
    }

    #[test]
    fn record_success_increments_existing() {
        let (cache, _dir) = fresh_cache();
        let key = [0xa2; 16];
        cache.record_success(&key, "simp; ring", 10).unwrap();
        cache.record_success(&key, "simp; ring", 14).unwrap();
        let rec = cache.get(&key).unwrap().unwrap();
        assert_eq!(rec.successes.len(), 1);
        assert_eq!(rec.successes[0].hits, 2);
        // average rounds toward 12
        assert!((10..=14).contains(&rec.successes[0].avg_elapsed_ms));
    }

    #[test]
    fn top_returns_in_hit_count_order() {
        let (cache, _dir) = fresh_cache();
        let key = [0xa3; 16];
        cache.record_success(&key, "ring", 10).unwrap();
        cache.record_success(&key, "linarith", 20).unwrap();
        cache.record_success(&key, "ring", 12).unwrap();
        let top = cache.top(&key, 5).unwrap();
        assert_eq!(top.len(), 2);
        assert_eq!(top[0].tactic_chain, "ring");
        assert_eq!(top[0].hits, 2);
        assert_eq!(top[1].tactic_chain, "linarith");
        assert_eq!(top[1].hits, 1);
    }

    #[test]
    fn top_respects_limit() {
        let (cache, _dir) = fresh_cache();
        let key = [0xa4; 16];
        cache.record_success(&key, "alpha", 1).unwrap();
        cache.record_success(&key, "beta", 1).unwrap();
        cache.record_success(&key, "gamma", 1).unwrap();
        let top = cache.top(&key, 2).unwrap();
        assert_eq!(top.len(), 2);
    }

    #[test]
    fn missing_key_get_returns_none() {
        let (cache, _dir) = fresh_cache();
        let key = [0xa5; 16];
        assert!(cache.get(&key).unwrap().is_none());
    }

    #[test]
    fn missing_key_top_returns_empty() {
        let (cache, _dir) = fresh_cache();
        let key = [0xa6; 16];
        assert!(cache.top(&key, 5).unwrap().is_empty());
    }
}
