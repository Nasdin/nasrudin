//! Cold-tier corpus backend for [`nasrudin_derive::AxiomStore`].
//!
//! ## Why a cold tier
//!
//! The Mathlib math-corpus extract has ~195k entries (~290 MB JSON).
//! Eager-loading it into a `HashMap<String, Axiom>` peaks at ~3.8 GB
//! of resident RAM during `serde_json::from_str` on the production
//! 4 GB droplet — boot OOMs and the API is unavailable. With this
//! cold tier:
//!
//! - The hot tier (in-memory `HashMap`) holds the ~3-5 k hand-coded
//!   postulates + PhysLean catalog entries that the GA's hot path
//!   touches every chunk.
//! - The cold tier (this module) holds the full 195 k Mathlib +
//!   Unknown corpus on disk in RocksDB. Lookups are point-fetches
//!   against [`CF_CORPUS_AXIOM`](super::CF_CORPUS_AXIOM) (bloom-filter-
//!   gated, ~5–50 µs warm); domain scans are range-iterations over
//!   [`CF_CORPUS_DOMAIN`](super::CF_CORPUS_DOMAIN).
//!
//! The shared block cache (configured in [`crate::TheoremDb::new`])
//! catches >95 % of lookups in steady state for the typical chunk
//! working set.
//!
//! ## Hydration
//!
//! First boot runs [`AxiomStore::hydrate_math_corpus_to_cold`](
//! ../../../derive/src/axiom_store.rs) which streams the JSON file
//! and `put_corpus_axiom`s in 1000-axiom batches. Subsequent boots
//! see `is_hydrated() == true` and skip the JSON parse entirely —
//! the hot tier loads in <100 ms and the cold tier is paged on
//! demand.

use anyhow::{Context, Result};
use nasrudin_core::{Axiom, Domain};
use rocksdb::{
    BlockBasedOptions, Cache, ColumnFamilyDescriptor, IteratorMode, Options, WriteBatch, DB,
};
use std::sync::Arc;

use super::{
    compute_block_cache_bytes, domain_to_key, CF_CORPUS_AXIOM, CF_CORPUS_DOMAIN, CF_CORPUS_META,
};

/// Schema/tagger version stamped into `CF_CORPUS_META` at the end of
/// hydration. Bumped to invalidate cold-tier data that was tagged
/// under a stale set of domain-prefix rules.
///
/// History:
/// - `"1"`: original Lean-side `DomainTagger` only (most PhysLean
///   flat-namespace theorems wrongly tagged `PureMath`; 0
///   ClassicalMechanics / Thermodynamics / etc).
/// - `"2"`: Rust-side `nasrudin_derive::domain_tagger::resolve_domain`
///   now overrides the JSON tag. Catches the full PhysLean v4.26.0
///   namespace surface (ClassicalMechanics, Cosmology→GR,
///   Thermodynamics, StatisticalMechanics, QFT family, etc).
pub const CORPUS_HYDRATION_VERSION: &[u8] = b"2";

/// Abstract cold-tier corpus interface used by
/// `nasrudin_derive::AxiomStore`. The derive crate doesn't see
/// RocksDB directly — it holds an `Arc<dyn CorpusBackend>` so unit
/// tests can mock the backend with an in-memory implementation.
///
/// Methods return owned `Axiom` values (decoded fresh from the
/// underlying store) — there's no stable borrow lifetime across a
/// RocksDB read.
pub trait CorpusBackend: Send + Sync {
    /// Look up a single axiom by name. Returns `Ok(None)` when the
    /// name isn't in the cold tier. The bloom filter on
    /// `CF_CORPUS_AXIOM` makes this RAM-speed for misses (~100 ns).
    fn get(&self, name: &str) -> Result<Option<Axiom>>;

    /// Batch lookup. Returns one entry per input name, in the same
    /// order, with `None` for misses. Implemented via `multi_get_cf`
    /// so a k-key fetch is one round-trip instead of k. Hot path for
    /// per-conjecture LLM-supplied axiom-set filtering, where the LLM
    /// can name 10–100 axioms whose first reference is a cold-tier
    /// disk seek.
    ///
    /// Default impl falls through to `get` per-name so backends that
    /// don't benefit from batching (e.g. the in-memory test mock) need
    /// no override.
    fn get_many(&self, names: &[&str]) -> Result<Vec<Option<Axiom>>> {
        names.iter().map(|n| self.get(n)).collect()
    }

    /// Iterate every cold-tier axiom in `CF_CORPUS_AXIOM` key order.
    /// The iterator is lazy — it pulls one axiom at a time so callers
    /// (e.g. `no_cheat_audit::audit`) can stream without loading
    /// 195k entries into RAM. Yields `Err` on a corrupt encoding;
    /// callers typically log and skip.
    fn iter(&self) -> Box<dyn Iterator<Item = Result<(String, Axiom)>> + '_>;

    /// Iterate cold-tier axioms whose `domain` matches `domain`.
    /// Range-scans `CF_CORPUS_DOMAIN` for the prefix
    /// `domain_str | 0x00`, then for each entry resolves the full
    /// `Axiom` from `CF_CORPUS_AXIOM`.
    fn iter_by_domain(
        &self,
        domain: &Domain,
    ) -> Box<dyn Iterator<Item = Result<(String, Axiom)>> + '_>;

    /// Total number of axioms in the cold tier. Reads the cached
    /// `count` meta key — O(1).
    fn count(&self) -> Result<u64>;

    /// `true` when the cold tier has been populated at least once.
    /// `AxiomStore` constructor uses this to decide whether to run
    /// hydration on first boot.
    fn is_hydrated(&self) -> Result<bool>;

    /// Insert a single axiom (writes both `CF_CORPUS_AXIOM` and the
    /// `CF_CORPUS_DOMAIN` index in one atomic `WriteBatch`).
    /// Idempotent — re-inserting the same name overwrites the value.
    /// Used by tests and ad-hoc registrations; the hot path is
    /// read-only so the GA never calls this.
    ///
    /// **Each call performs a WAL fsync.** For bulk hydration use
    /// [`Self::put_many`] which writes a whole batch in one fsync,
    /// ~10× faster on slow storage (Pi SD card).
    fn put(&self, axiom: &Axiom) -> Result<()>;

    /// Bulk-insert a batch of axioms in **one atomic `WriteBatch`**.
    /// All `CF_CORPUS_AXIOM` writes + all `CF_CORPUS_DOMAIN` index
    /// writes commit together with a single fsync at the end.
    ///
    /// `wal_disabled = true` skips the WAL entirely for the batch —
    /// safe during hydration because `finish_hydration` writes the
    /// `count` meta key WITH the WAL after all data lands; if we
    /// crash mid-hydration the cold tier on next boot has no
    /// `count`/`hydrated_at` and we re-hydrate from scratch (the
    /// dump is idempotent). On a Pi SD card this turns ~1000 fsyncs
    /// per batch into one — minutes-of-hydration → seconds.
    fn put_many(&self, axioms: &[Axiom], wal_disabled: bool) -> Result<()>;

    /// Read a meta-CF key. Used for ETag persistence (worker side)
    /// and version probing (server side). Bytes are returned as-is;
    /// callers parse to UTF-8 / integer / etc. as needed.
    fn meta_get(&self, key: &str) -> Result<Option<Vec<u8>>>;

    /// Write a meta-CF key. Companion to [`Self::meta_get`].
    /// Single-key fsync — fine for infrequent writes (one per
    /// hydration completion, one per ETag refresh).
    fn meta_put(&self, key: &str, value: &[u8]) -> Result<()>;

    /// Mark the cold tier hydrated and persist the running count.
    /// Called by the hydrator at end-of-stream so subsequent boots
    /// short-circuit the JSON parse.
    fn finish_hydration(&self, total: u64) -> Result<()>;

    /// Delete every row in `CF_CORPUS_AXIOM` and `CF_CORPUS_DOMAIN`
    /// (and clear the relevant meta keys) to prepare for a fresh
    /// re-hydration. Used when `CORPUS_HYDRATION_VERSION` bumps and
    /// the stored data is tagged under a stale rule set.
    ///
    /// **Why this exists:** `put`/`put_many` only write the new
    /// `{new_domain}|{name}` key into `CF_CORPUS_DOMAIN`. If the
    /// same `name` previously had a different domain, the old
    /// `{old_domain}|{name}` row sticks around and pollutes
    /// `iter_by_domain` queries. A clean wipe before re-hydration
    /// guarantees the index reflects only the current tags.
    fn wipe_for_rehydration(&self) -> Result<()>;

    /// Snapshot every axiom name into a `Vec<String>`. Used by the
    /// AxiomStore's mutation hot path: `store.iter().choose(rng)` on
    /// 195k entries is O(N) and re-iterates RocksDB every call. We
    /// cache this list in-process at construction time so name picks
    /// become O(1) + a single RocksDB point-lookup. Bounded
    /// memory: 195k × ~30 B avg = ~6 MB.
    fn snapshot_names(&self) -> Result<Vec<String>>;
}

/// RocksDB-backed corpus store. Holds an `Arc<DB>` so it can be
/// constructed from an existing [`TheoremDb`](super::TheoremDb)
/// (`CorpusDb::on_existing_db(db.shared_db())`) — a separate
/// RocksDB instance would defeat the shared block-cache budget.
pub struct CorpusDb {
    db: Arc<DB>,
}

impl CorpusDb {
    /// Wrap an existing RocksDB handle. The caller's `TheoremDb` and
    /// the returned `CorpusDb` share the same block cache (configured
    /// at `TheoremDb::new` open time), the same column-family
    /// registry, and the same on-disk write-ahead log. This is the
    /// preferred constructor for the API server, where the cold tier
    /// rides on the same RocksDB instance as the theorem store.
    pub fn on_existing_db(db: Arc<DB>) -> Self {
        Self { db }
    }

    /// Open a standalone CorpusDb at `path` — used by the **worker**
    /// where there's no `TheoremDb` to share with. Opens only the
    /// three corpus column families (`CF_CORPUS_AXIOM`,
    /// `CF_CORPUS_DOMAIN`, `CF_CORPUS_META`) plus the implicit default
    /// CF, with the same dynamic block-cache sizing
    /// ([`compute_block_cache_bytes`]) and bloom-filter / point-lookup
    /// optimisation as the API server's setup.
    ///
    /// Why a separate constructor instead of just calling `TheoremDb::new`:
    /// the worker's RocksDB only holds the cold-tier corpus — it doesn't
    /// participate in theorem CRUD, the reverify queue, the verified-at
    /// recency index, etc. Opening 12+ unused CFs would waste table-cache
    /// slots and double our open-file budget on the Pi. The worker only
    /// needs the corpus tier, so we open exactly that.
    ///
    /// On the 1 GB Raspberry Pi target, `compute_block_cache_bytes()`
    /// returns the 64 MB floor — enough to hold ~50–100 MB of hot corpus
    /// pages plus the bloom filter + index blocks for the ~195k-entry
    /// `CF_CORPUS_AXIOM`. Steady-state working-set hit rate stays >95%
    /// for the typical 5–20 k-axiom GA chunk.
    pub fn open_standalone(path: &std::path::Path) -> Result<Self> {
        let mut db_opts = Options::default();
        db_opts.create_if_missing(true);
        db_opts.create_missing_column_families(true);

        let (cache_bytes, total_bytes) = compute_block_cache_bytes();
        let block_cache = Cache::new_lru_cache(cache_bytes);
        if total_bytes > 0 {
            tracing::info!(
                "Worker RocksDB block cache: {} MB ({}% of {} MB system RAM)",
                cache_bytes / (1024 * 1024),
                cache_bytes * 100 / total_bytes,
                total_bytes / (1024 * 1024),
            );
        } else {
            tracing::info!(
                "Worker RocksDB block cache: {} MB (env override / fallback)",
                cache_bytes / (1024 * 1024),
            );
        }

        // Build descriptors: corpus_axiom gets the bloom + point-lookup
        // optimisation; the index and meta CFs are plain block-table.
        let cf_descriptors: Vec<ColumnFamilyDescriptor> = [
            CF_CORPUS_AXIOM,
            CF_CORPUS_DOMAIN,
            CF_CORPUS_META,
        ]
        .iter()
        .map(|name| {
            let mut cf_opts = Options::default();
            let mut block_opts = BlockBasedOptions::default();
            block_opts.set_block_cache(&block_cache);
            if *name == CF_CORPUS_AXIOM {
                block_opts.set_bloom_filter(10.0, false);
                block_opts.set_whole_key_filtering(true);
                cf_opts.set_block_based_table_factory(&block_opts);
                cf_opts.optimize_for_point_lookup(64);
            } else {
                cf_opts.set_block_based_table_factory(&block_opts);
            }
            ColumnFamilyDescriptor::new(*name, cf_opts)
        })
        .collect();

        let db = DB::open_cf_descriptors(&db_opts, path, cf_descriptors)
            .with_context(|| format!("open standalone CorpusDb at {}", path.display()))?;
        Ok(Self { db: Arc::new(db) })
    }

    /// Build the secondary-index key:
    /// `domain_str | 0x00 | axiom_name_bytes`.
    fn domain_key(domain_str: &str, name: &str) -> Vec<u8> {
        let mut k = Vec::with_capacity(domain_str.len() + 1 + name.len());
        k.extend_from_slice(domain_str.as_bytes());
        k.push(0u8);
        k.extend_from_slice(name.as_bytes());
        k
    }
}

impl CorpusBackend for CorpusDb {
    fn get(&self, name: &str) -> Result<Option<Axiom>> {
        let cf = self
            .db
            .cf_handle(CF_CORPUS_AXIOM)
            .context("Missing corpus_axiom CF")?;
        match self.db.get_cf(&cf, name.as_bytes()).context("get corpus axiom")? {
            Some(bytes) => {
                let axiom: Axiom = rkyv::from_bytes::<Axiom, rkyv::rancor::Error>(&bytes)
                    .map_err(|e| anyhow::anyhow!("rkyv corpus axiom decode: {e}"))?;
                Ok(Some(axiom))
            }
            None => Ok(None),
        }
    }

    fn get_many(&self, names: &[&str]) -> Result<Vec<Option<Axiom>>> {
        if names.is_empty() {
            return Ok(Vec::new());
        }
        let cf = self
            .db
            .cf_handle(CF_CORPUS_AXIOM)
            .context("Missing corpus_axiom CF")?;
        // multi_get_cf takes (cf, key) pairs and returns one Result<Option<DBVector>>
        // per input. One PG-bag-style round-trip to RocksDB regardless of k.
        let pairs: Vec<(_, &[u8])> =
            names.iter().map(|n| (&cf, n.as_bytes())).collect();
        let results = self.db.multi_get_cf(pairs);
        let mut out = Vec::with_capacity(results.len());
        for r in results {
            match r.context("multi_get corpus axiom")? {
                Some(bytes) => {
                    let axiom: Axiom = rkyv::from_bytes::<Axiom, rkyv::rancor::Error>(&bytes)
                        .map_err(|e| anyhow::anyhow!("rkyv corpus axiom decode: {e}"))?;
                    out.push(Some(axiom));
                }
                None => out.push(None),
            }
        }
        Ok(out)
    }

    fn iter(&self) -> Box<dyn Iterator<Item = Result<(String, Axiom)>> + '_> {
        let cf = match self.db.cf_handle(CF_CORPUS_AXIOM) {
            Some(cf) => cf,
            None => return Box::new(std::iter::empty()),
        };
        let inner = self.db.iterator_cf(&cf, IteratorMode::Start);
        Box::new(inner.map(|item| {
            let (k, v) = item.context("iter corpus_axiom")?;
            let name = String::from_utf8(k.to_vec())
                .context("corpus_axiom key not utf8")?;
            let axiom: Axiom = rkyv::from_bytes::<Axiom, rkyv::rancor::Error>(&v)
                .map_err(|e| anyhow::anyhow!("rkyv corpus axiom decode: {e}"))?;
            Ok((name, axiom))
        }))
    }

    fn iter_by_domain(
        &self,
        domain: &Domain,
    ) -> Box<dyn Iterator<Item = Result<(String, Axiom)>> + '_> {
        let domain_str = domain_to_key(domain);
        // Prefix is `domain_str | 0x00` — anything starting with this
        // is in the requested domain.
        let mut prefix = domain_str.clone().into_bytes();
        prefix.push(0u8);

        let idx_cf = match self.db.cf_handle(CF_CORPUS_DOMAIN) {
            Some(cf) => cf,
            None => return Box::new(std::iter::empty()),
        };
        // Verify CF_CORPUS_AXIOM exists once up front; the per-item
        // closure re-resolves on each call (cheap pointer fetch) since
        // the borrow doesn't escape this function's lifetime.
        if self.db.cf_handle(CF_CORPUS_AXIOM).is_none() {
            return Box::new(std::iter::empty());
        }
        let db = Arc::clone(&self.db);
        let prefix_for_filter = prefix.clone();
        let inner = self
            .db
            .prefix_iterator_cf(&idx_cf, &prefix)
            .take_while(move |item| match item {
                Ok((k, _)) => k.starts_with(&prefix_for_filter),
                Err(_) => true,
            });
        Box::new(inner.map(move |item| {
            let (k, _) = item.context("iter corpus_domain")?;
            // Strip prefix to recover the axiom name.
            let name_bytes = &k[prefix.len()..];
            let name = std::str::from_utf8(name_bytes)
                .context("corpus_domain index name not utf8")?
                .to_string();
            let axiom_cf = db
                .cf_handle(CF_CORPUS_AXIOM)
                .context("Missing corpus_axiom CF on lookup")?;
            let payload = db
                .get_cf(&axiom_cf, name.as_bytes())
                .context("get corpus_axiom for domain index")?
                .ok_or_else(|| {
                    anyhow::anyhow!("corpus_domain points to missing axiom: {name}")
                })?;
            let axiom: Axiom = rkyv::from_bytes::<Axiom, rkyv::rancor::Error>(&payload)
                .map_err(|e| anyhow::anyhow!("rkyv corpus axiom decode: {e}"))?;
            Ok((name, axiom))
        }))
    }

    fn count(&self) -> Result<u64> {
        let cf = self
            .db
            .cf_handle(CF_CORPUS_META)
            .context("Missing corpus_meta CF")?;
        match self.db.get_cf(&cf, b"count").context("get corpus_meta count")? {
            Some(v) => {
                let s = std::str::from_utf8(&v).context("count meta not utf8")?;
                Ok(s.parse::<u64>().unwrap_or(0))
            }
            None => Ok(0),
        }
    }

    fn is_hydrated(&self) -> Result<bool> {
        let cf = self
            .db
            .cf_handle(CF_CORPUS_META)
            .context("Missing corpus_meta CF")?;
        let hydrated_at = self
            .db
            .get_cf(&cf, b"hydrated_at")
            .context("get corpus_meta hydrated_at")?;
        if hydrated_at.is_none() {
            return Ok(false);
        }
        // Version check — re-hydrate if the stored schema/tagger
        // version is older than what this binary expects. See
        // `CORPUS_HYDRATION_VERSION` for the changelog.
        let version = self
            .db
            .get_cf(&cf, b"version")
            .context("get corpus_meta version")?;
        match version {
            Some(v) if v.as_slice() == CORPUS_HYDRATION_VERSION => Ok(true),
            other => {
                let observed = other
                    .as_ref()
                    .and_then(|v| std::str::from_utf8(v).ok())
                    .unwrap_or("<none>");
                let expected = std::str::from_utf8(CORPUS_HYDRATION_VERSION).unwrap_or("?");
                tracing::warn!(
                    observed,
                    expected,
                    "Cold-tier corpus version mismatch — re-hydration required"
                );
                Ok(false)
            }
        }
    }

    fn put(&self, axiom: &Axiom) -> Result<()> {
        let mut batch = WriteBatch::default();
        let axiom_cf = self
            .db
            .cf_handle(CF_CORPUS_AXIOM)
            .context("Missing corpus_axiom CF")?;
        let domain_cf = self
            .db
            .cf_handle(CF_CORPUS_DOMAIN)
            .context("Missing corpus_domain CF")?;

        let value = rkyv::to_bytes::<rkyv::rancor::Error>(axiom)
            .map_err(|e| anyhow::anyhow!("rkyv corpus axiom encode: {e}"))?;
        batch.put_cf(&axiom_cf, axiom.name.as_bytes(), value.as_slice());

        let domain_str = domain_to_key(&axiom.domain);
        let dkey = Self::domain_key(&domain_str, &axiom.name);
        batch.put_cf(&domain_cf, &dkey, b"");

        self.db.write(batch).context("write corpus batch")?;
        Ok(())
    }

    fn put_many(&self, axioms: &[Axiom], wal_disabled: bool) -> Result<()> {
        if axioms.is_empty() {
            return Ok(());
        }
        let axiom_cf = self
            .db
            .cf_handle(CF_CORPUS_AXIOM)
            .context("Missing corpus_axiom CF")?;
        let domain_cf = self
            .db
            .cf_handle(CF_CORPUS_DOMAIN)
            .context("Missing corpus_domain CF")?;

        let mut batch = WriteBatch::default();
        for axiom in axioms {
            let value = rkyv::to_bytes::<rkyv::rancor::Error>(axiom)
                .map_err(|e| anyhow::anyhow!("rkyv corpus axiom encode {}: {e}", axiom.name))?;
            batch.put_cf(&axiom_cf, axiom.name.as_bytes(), value.as_slice());

            let domain_str = domain_to_key(&axiom.domain);
            let dkey = Self::domain_key(&domain_str, &axiom.name);
            batch.put_cf(&domain_cf, &dkey, b"");
        }

        if wal_disabled {
            // WAL disabled: durability is provided by `finish_hydration`'s
            // count/hydrated_at write at the end of the stream. If we
            // crash here, count/hydrated_at are missing and the next
            // boot re-hydrates (idempotent). This trades crash-recovery
            // granularity for ~10× hydration speed on slow SD cards.
            let mut opts = rocksdb::WriteOptions::default();
            opts.disable_wal(true);
            self.db
                .write_opt(batch, &opts)
                .context("write corpus batch (no-WAL)")?;
        } else {
            self.db.write(batch).context("write corpus batch")?;
        }
        Ok(())
    }

    fn meta_get(&self, key: &str) -> Result<Option<Vec<u8>>> {
        let cf = self
            .db
            .cf_handle(CF_CORPUS_META)
            .context("Missing corpus_meta CF")?;
        Ok(self
            .db
            .get_cf(&cf, key.as_bytes())
            .context("get corpus_meta key")?)
    }

    fn meta_put(&self, key: &str, value: &[u8]) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_CORPUS_META)
            .context("Missing corpus_meta CF")?;
        self.db
            .put_cf(&cf, key.as_bytes(), value)
            .context("put corpus_meta key")?;
        Ok(())
    }

    fn finish_hydration(&self, total: u64) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_CORPUS_META)
            .context("Missing corpus_meta CF")?;
        self.db
            .put_cf(&cf, b"count", total.to_string().as_bytes())
            .context("put corpus_meta count")?;
        let now = chrono::Utc::now().to_rfc3339();
        self.db
            .put_cf(&cf, b"hydrated_at", now.as_bytes())
            .context("put corpus_meta hydrated_at")?;
        // Bump the version key so future schema migrations can
        // detect a downlevel cold tier and re-hydrate. See
        // `CORPUS_HYDRATION_VERSION` for the changelog.
        self.db
            .put_cf(&cf, b"version", CORPUS_HYDRATION_VERSION)
            .context("put corpus_meta version")?;
        Ok(())
    }

    fn wipe_for_rehydration(&self) -> Result<()> {
        let axiom_cf = self
            .db
            .cf_handle(CF_CORPUS_AXIOM)
            .context("Missing corpus_axiom CF")?;
        let domain_cf = self
            .db
            .cf_handle(CF_CORPUS_DOMAIN)
            .context("Missing corpus_domain CF")?;
        let meta_cf = self
            .db
            .cf_handle(CF_CORPUS_META)
            .context("Missing corpus_meta CF")?;
        // Bound the empty range with the largest u8 prefix so
        // `delete_range_cf` covers all keys (RocksDB's delete-range
        // is `[from, to)`). Two CFs, no row-by-row iteration —
        // O(SST-file metadata) instead of O(N).
        let lo: [u8; 0] = [];
        let hi: [u8; 16] = [0xFF; 16];
        let mut batch = WriteBatch::default();
        batch.delete_range_cf(&axiom_cf, &lo[..], &hi[..]);
        batch.delete_range_cf(&domain_cf, &lo[..], &hi[..]);
        // Clear meta markers so `is_hydrated()` stays `false` until
        // `finish_hydration` re-stamps them at end-of-stream.
        batch.delete_cf(&meta_cf, b"hydrated_at");
        batch.delete_cf(&meta_cf, b"count");
        batch.delete_cf(&meta_cf, b"version");
        self.db
            .write(batch)
            .context("wipe corpus_axiom + corpus_domain + corpus_meta markers")?;
        // Force a flush so the deletes hit disk before the
        // re-hydration's writes start — otherwise a crash during
        // re-hydration could leave a CF in a half-deleted state
        // that the next boot reads as "live but stale".
        self.db
            .flush_cf(&axiom_cf)
            .context("flush corpus_axiom after wipe")?;
        self.db
            .flush_cf(&domain_cf)
            .context("flush corpus_domain after wipe")?;
        self.db
            .flush_cf(&meta_cf)
            .context("flush corpus_meta after wipe")?;
        tracing::warn!("Cold-tier corpus wiped for re-hydration under new tagger version");
        Ok(())
    }

    fn snapshot_names(&self) -> Result<Vec<String>> {
        let cf = self
            .db
            .cf_handle(CF_CORPUS_AXIOM)
            .context("Missing corpus_axiom CF")?;
        let mut names = Vec::new();
        for item in self.db.iterator_cf(&cf, IteratorMode::Start) {
            let (k, _) = item.context("iter corpus_axiom for snapshot_names")?;
            let name = String::from_utf8(k.to_vec())
                .context("corpus_axiom key not utf8 in snapshot_names")?;
            names.push(name);
        }
        Ok(names)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TheoremDb;
    use nasrudin_core::{BinOp, Domain, Expr};
    use tempfile::TempDir;

    fn open() -> (TheoremDb, CorpusDb, TempDir) {
        let tmp = TempDir::new().unwrap();
        let db = TheoremDb::new(tmp.path().to_str().unwrap()).unwrap();
        let cdb = CorpusDb::on_existing_db(db.shared_db());
        (db, cdb, tmp)
    }

    fn mk(name: &str, domain: Domain) -> Axiom {
        Axiom {
            name: name.to_string(),
            domain,
            statement: Expr::BinOp(
                BinOp::Eq,
                Box::new(Expr::Var(name.to_string())),
                Box::new(Expr::Lit(0, 1)),
            ),
            description: format!("doc for {name}"),
        }
    }

    #[test]
    fn write_then_read_round_trip() {
        let (_db, cdb, _tmp) = open();
        for i in 0..100 {
            let dom = if i % 3 == 0 {
                Domain::PureMath
            } else {
                Domain::SpecialRelativity
            };
            cdb.put(&mk(&format!("ax_{i}"), dom)).unwrap();
        }
        cdb.finish_hydration(100).unwrap();

        assert_eq!(cdb.count().unwrap(), 100);
        assert!(cdb.is_hydrated().unwrap());

        // Point lookup hit
        let ax = cdb.get("ax_42").unwrap().unwrap();
        assert_eq!(ax.name, "ax_42");
        assert_eq!(ax.domain, Domain::PureMath); // 42 % 3 == 0

        // Point lookup miss
        assert!(cdb.get("nonexistent").unwrap().is_none());

        // Full iter
        let all: Vec<_> = cdb.iter().filter_map(|r| r.ok()).collect();
        assert_eq!(all.len(), 100);

        // by_domain index
        let pm: Vec<_> = cdb
            .iter_by_domain(&Domain::PureMath)
            .filter_map(|r| r.ok())
            .collect();
        assert_eq!(pm.len(), 34); // 0, 3, ..., 99 → 34 entries
        for (_, a) in &pm {
            assert_eq!(a.domain, Domain::PureMath);
        }
        let sr: Vec<_> = cdb
            .iter_by_domain(&Domain::SpecialRelativity)
            .filter_map(|r| r.ok())
            .collect();
        assert_eq!(sr.len(), 66);

        // snapshot_names returns every name
        let names = cdb.snapshot_names().unwrap();
        assert_eq!(names.len(), 100);
        assert!(names.contains(&"ax_0".to_string()));
    }

    #[test]
    fn fresh_db_is_not_hydrated() {
        let (_db, cdb, _tmp) = open();
        assert!(!cdb.is_hydrated().unwrap());
        assert_eq!(cdb.count().unwrap(), 0);
    }

    #[test]
    fn domain_separator_does_not_bleed() {
        // A regression test for the 0x00 separator: without it, a
        // prefix scan for "special_relativity" could match
        // "special_relativity_extras" or any other domain whose key
        // is a prefix.
        let (_db, cdb, _tmp) = open();
        cdb.put(&mk("real_axiom", Domain::SpecialRelativity)).unwrap();
        // Synthesize a different domain whose `domain_to_key` happens
        // to start with "special" — Domain::CrossDomain([SR, ...])
        // produces "cross:special_relativity+...". No risk of bleed,
        // but assert the round trip anyway.
        let cross = Domain::CrossDomain(vec![
            Domain::SpecialRelativity,
            Domain::PureMath,
        ]);
        cdb.put(&mk("cross_axiom", cross.clone())).unwrap();
        let sr: Vec<_> = cdb
            .iter_by_domain(&Domain::SpecialRelativity)
            .filter_map(|r| r.ok())
            .collect();
        assert_eq!(sr.len(), 1, "SR should not match cross: prefix");
        assert_eq!(sr[0].1.name, "real_axiom");
    }
}
