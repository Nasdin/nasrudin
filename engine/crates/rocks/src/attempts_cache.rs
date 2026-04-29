//! RocksDB-backed cache of verification attempt outcomes.
//!
//! ## Key
//!
//! 16 bytes: `(canonical_hash || axiom_set_hash)`.
//! - `canonical_hash` (8 bytes) — `Theorem.canonical_hash` for the candidate.
//! - `axiom_set_hash` (8 bytes) — BLAKE3 over the sorted axiom IDs that are
//!   in scope when the attempt is made. Caller computes both.
//!
//! ## Value
//!
//! `serde_json`-encoded `AttemptRecord`.
//!
//! ## TTL
//!
//! RocksDB has no native TTL on a CF created without TTL options; we read
//! the timestamp on the record and treat expired rows as cache misses
//! (`get_with_ttl`). Storage isn't reclaimed until a future compaction
//! sweep — this is fine for a 30-day window where the working set is
//! still small relative to the disk budget.

use anyhow::{Context, Result};
use chrono::{DateTime, Duration, Utc};
use rocksdb::DB;
use serde::{Deserialize, Serialize};

const CF_ATTEMPTS: &str = "attempts";

/// One outcome enum value for an attempted verification.
///
/// `Verified` carries the resulting theorem's 8-byte id and the tactic
/// chain that proved it. `RejectedTypeError` carries a truncated stderr
/// (so we don't bloat the value with multi-MB Lean panics). The other
/// rejection variants are self-explanatory.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(tag = "kind", content = "data", rename_all = "snake_case")]
pub enum AttemptOutcome {
    Verified { theorem_id: [u8; 8], tactic: String },
    RejectedTypeError { msg: String },
    RejectedTimeout,
    RejectedTrivial { reason: String },
    Pending,
}

/// One row in the attempts cache.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AttemptRecord {
    pub outcome: AttemptOutcome,
    pub lean_version: String,
    pub timestamp: DateTime<Utc>,
    pub attempted_by: String,
    pub elapsed_ms: u32,
}

/// RocksDB wrapper for the `attempts` column family.
///
/// In tests, opens a fresh standalone RocksDB containing only the
/// `attempts` CF (via [`AttemptsCache::open`]). In production, the cache
/// is intended to share the engine's main `TheoremDb` instance — that
/// integration lives in Phase A.5 (out of scope for this module).
pub struct AttemptsCache {
    db: DB,
}

impl AttemptsCache {
    /// Open a standalone RocksDB at `path` containing only the `attempts` CF.
    pub fn open(path: &str) -> Result<Self> {
        use rocksdb::{ColumnFamilyDescriptor, Options};
        let mut opts = Options::default();
        opts.create_if_missing(true);
        opts.create_missing_column_families(true);
        let cf = ColumnFamilyDescriptor::new(CF_ATTEMPTS, Options::default());
        let db = DB::open_cf_descriptors(&opts, path, vec![cf])
            .context("open attempts cache db")?;
        Ok(Self { db })
    }

    /// Concatenate the two 8-byte hashes into the 16-byte key.
    pub fn make_key(canonical_hash: &[u8; 8], axiom_set_hash: &[u8; 8]) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(canonical_hash);
        out[8..].copy_from_slice(axiom_set_hash);
        out
    }

    /// Put a record. Caller-supplied key, no TTL enforcement on write.
    pub fn put(&self, key: &[u8; 16], record: &AttemptRecord) -> Result<()> {
        let cf = self.db.cf_handle(CF_ATTEMPTS).context("cf attempts")?;
        let bytes = serde_json::to_vec(record).context("serialise AttemptRecord")?;
        self.db.put_cf(&cf, key, bytes).context("put attempts")?;
        Ok(())
    }

    /// Get the record at `key`, ignoring TTL.
    pub fn get(&self, key: &[u8; 16]) -> Result<Option<AttemptRecord>> {
        let cf = self.db.cf_handle(CF_ATTEMPTS).context("cf attempts")?;
        match self.db.get_cf(&cf, key).context("get attempts")? {
            Some(bytes) => Ok(Some(
                serde_json::from_slice(&bytes).context("deserialise AttemptRecord")?,
            )),
            None => Ok(None),
        }
    }

    /// Get the record at `key`, treating any record older than `max_age`
    /// as a cache miss (returns `Ok(None)`).
    pub fn get_with_ttl(&self, key: &[u8; 16], max_age: Duration) -> Result<Option<AttemptRecord>> {
        match self.get(key)? {
            Some(rec) if Utc::now() - rec.timestamp <= max_age => Ok(Some(rec)),
            _ => Ok(None),
        }
    }

    /// Lookup-or-compute: on cache hit (within TTL), return the cached record.
    /// On miss, run `compute()`, build a record stamped with now / version /
    /// elapsed / worker, persist it, and return it.
    ///
    /// Caller is responsible for building the 16-byte key via `make_key`.
    pub fn lookup_or_compute<F>(
        &self,
        key: &[u8; 16],
        max_age: Duration,
        attempted_by: &str,
        lean_version: &str,
        compute: F,
    ) -> Result<AttemptRecord>
    where
        F: FnOnce() -> AttemptOutcome,
    {
        if let Some(hit) = self.get_with_ttl(key, max_age)? {
            return Ok(hit);
        }
        let started = std::time::Instant::now();
        let outcome = compute();
        let elapsed_ms = u32::try_from(started.elapsed().as_millis()).unwrap_or(u32::MAX);
        let record = AttemptRecord {
            outcome,
            lean_version: lean_version.to_string(),
            timestamp: Utc::now(),
            attempted_by: attempted_by.to_string(),
            elapsed_ms,
        };
        self.put(key, &record)?;
        Ok(record)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    fn fresh_cache() -> (AttemptsCache, tempfile::TempDir) {
        let dir = tempdir().unwrap();
        let cache = AttemptsCache::open(dir.path().to_str().unwrap()).unwrap();
        (cache, dir)
    }

    #[test]
    fn put_then_get_roundtrips() {
        let (cache, _dir) = fresh_cache();
        let key = [1u8; 16];
        let record = AttemptRecord {
            outcome: AttemptOutcome::Verified {
                theorem_id: [0xab; 8],
                tactic: "ring".into(),
            },
            lean_version: "4.27.0".into(),
            timestamp: Utc::now(),
            attempted_by: "test-worker".into(),
            elapsed_ms: 42,
        };
        cache.put(&key, &record).unwrap();
        let got = cache.get(&key).unwrap().unwrap();
        assert!(matches!(got.outcome, AttemptOutcome::Verified { .. }));
        assert_eq!(got.elapsed_ms, 42);
        assert_eq!(got.lean_version, "4.27.0");
    }

    #[test]
    fn missing_key_returns_none() {
        let (cache, _dir) = fresh_cache();
        let key = [9u8; 16];
        assert!(cache.get(&key).unwrap().is_none());
    }

    #[test]
    fn expired_record_treated_as_miss() {
        let (cache, _dir) = fresh_cache();
        let key = [2u8; 16];
        let stale = AttemptRecord {
            outcome: AttemptOutcome::RejectedTimeout,
            lean_version: "4.27.0".into(),
            timestamp: Utc::now() - Duration::days(31),
            attempted_by: "test-worker".into(),
            elapsed_ms: 0,
        };
        cache.put(&key, &stale).unwrap();
        let got = cache.get_with_ttl(&key, Duration::days(30)).unwrap();
        assert!(got.is_none(), "30-day-old record should be treated as expired");
    }

    #[test]
    fn key_helper_concatenates() {
        let canonical = [0xaa; 8];
        let axiom_set = [0xbb; 8];
        let key = AttemptsCache::make_key(&canonical, &axiom_set);
        assert_eq!(&key[..8], &canonical);
        assert_eq!(&key[8..], &axiom_set);
    }

    #[test]
    fn fresh_record_passes_ttl() {
        let (cache, _dir) = fresh_cache();
        let key = [3u8; 16];
        let fresh = AttemptRecord {
            outcome: AttemptOutcome::RejectedTimeout,
            lean_version: "4.27.0".into(),
            timestamp: Utc::now() - Duration::seconds(10),
            attempted_by: "test-worker".into(),
            elapsed_ms: 0,
        };
        cache.put(&key, &fresh).unwrap();
        let got = cache.get_with_ttl(&key, Duration::days(30)).unwrap();
        assert!(got.is_some(), "10-second-old record should pass a 30-day TTL");
    }

    #[test]
    fn lookup_or_compute_misses_then_hits() {
        let (cache, _dir) = fresh_cache();
        let key = [3u8; 16];
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

        assert_eq!(
            compute_calls, 1,
            "second call should hit cache, not recompute"
        );
    }
}
