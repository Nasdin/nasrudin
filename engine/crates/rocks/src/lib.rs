//! RocksDB storage backend for the Physics Generator theorem database.
//!
//! Provides persistent storage for theorems, proofs, and lineage data using
//! column families for efficient indexed access by domain, depth, generation, etc.

use anyhow::{Context, Result};
use nasrudin_core::{Domain, ProofTree, Theorem, TheoremId, VerificationStatus};
use rocksdb::{BlockBasedOptions, Cache, ColumnFamilyDescriptor, IteratorMode, Options, WriteBatch, DB};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

pub mod attempts_cache;
pub use attempts_cache::{AttemptOutcome, AttemptRecord, AttemptsCache};
pub mod corpus;
pub use corpus::{CorpusBackend, CorpusDb};
pub mod tactic_priors;
pub use tactic_priors::{TacticPriorRecord, TacticPriorsCache, TacticSuccess};

/// Column family names used by the theorem database.
const CF_THEOREMS: &str = "theorems";
const CF_PROOFS: &str = "proofs";
const CF_LINEAGE: &str = "lineage";
const CF_BY_DOMAIN: &str = "by_domain";
const CF_BY_DEPTH: &str = "by_depth";
const CF_BY_AXIOM: &str = "by_axiom";
const CF_BY_GENERATION: &str = "by_generation";
const CF_LATEX_INDEX: &str = "latex_index";
const CF_STATS: &str = "stats";
const CF_REVERIFY_QUEUE: &str = "reverify_queue";
const CF_ATTEMPTS: &str = "attempts";
const CF_TACTIC_PRIORS: &str = "tactic_priors";
/// Pending PG-insert queue. Populated by `/api/ingest` on the hot path
/// (RocksDB-primary write-behind), drained by the background `pg_drain`
/// task. Keys are theorem_ids, values are bincode-serialised
/// `PgInsertQueueEntry` payloads. On boot, the API scans this CF and
/// re-enqueues anything that wasn't yet persisted to PG before the
/// previous shutdown — so an API crash never loses a verified theorem.
const CF_PG_INSERT_QUEUE: &str = "pg_insert_queue";
/// Cold-tier corpus axiom store. Holds the ~195k Mathlib + Unknown
/// entries that previously lived in the in-memory `AxiomStore`'s
/// `HashMap`. `key = axiom_name_bytes`, `value = bincode(Axiom)`. Keeps
/// API-process resident RAM bounded — the AxiomStore's hot tier
/// remains the ~3-5 k hand-coded postulates + PhysLean catalog
/// entries; the cold tier is paged on demand from this CF.
pub(crate) const CF_CORPUS_AXIOM: &str = "corpus_axiom";
/// Secondary index over `CF_CORPUS_AXIOM` for `by_domain` range scans.
/// `key = domain_str | 0x00 | axiom_name_bytes`, `value = []` (empty —
/// the key contains everything, the actual axiom payload comes from a
/// follow-up `CF_CORPUS_AXIOM` lookup). The 0x00 separator guarantees
/// that a `prefix_iterator_cf("special_relativity\0")` doesn't bleed
/// into `"special_relativity_extras"` etc.
pub(crate) const CF_CORPUS_DOMAIN: &str = "corpus_domain";
/// Meta-state for the corpus CF: hydration version, total count,
/// timestamp of the last hydration. JSON values keyed by string
/// (`"version"`, `"count"`, `"hydrated_at"`).
pub(crate) const CF_CORPUS_META: &str = "corpus_meta";
/// Newest-first index over verified theorems for `/api/seed` and
/// `/api/theorems/recent`. Keyed by `(verified_at_be_micros, theorem_id)`
/// so a reverse iter yields most-recent-first. Written atomically
/// alongside CF_THEOREMS when a theorem transitions to Verified.
const CF_BY_VERIFIED_AT: &str = "by_verified_at";
/// Lazy lake-promotion queue (P-Task 2). Holds theorems awaiting
/// kernel-level verification. Three priority lanes:
///   0 = manual user trigger / synchronous download
///   1 = seed-inclusion demand (worker polled /api/seed and we need
///       this theorem promoted before peers can build on it)
///   2 = background crawler (eventually-consistent promotion of
///       every ChainVerified row regardless of usage)
/// Keys are `[priority_u8, enqueued_at_be_u64, theorem_id_8]`. A
/// forward iter from `[0u8]` yields highest-priority oldest first.
const CF_LAKE_PROMOTION_QUEUE: &str = "lake_promotion_queue";
/// Reverse-dependency index for derivation acyclicity. For every
/// theorem T whose proof transitively cites ancestor A, we write
/// key `A_id (8) || T_id (8)` with empty value. A `prefix_iterator_cf`
/// keyed on `A_id` yields every T that depends on A — used by
/// `forbidden_for_target` to filter the premise set when re-deriving A
/// (or anything in A's class). Fixed-width keys mean no separator
/// byte and no value payload — the cheapest possible edge index.
const CF_REVERSE_DEPS: &str = "reverse_deps";

const ALL_CFS: &[&str] = &[
    CF_THEOREMS,
    CF_PROOFS,
    CF_LINEAGE,
    CF_BY_DOMAIN,
    CF_BY_DEPTH,
    CF_BY_AXIOM,
    CF_BY_GENERATION,
    CF_LATEX_INDEX,
    CF_STATS,
    CF_REVERIFY_QUEUE,
    CF_ATTEMPTS,
    CF_TACTIC_PRIORS,
    CF_PG_INSERT_QUEUE,
    CF_BY_VERIFIED_AT,
    CF_LAKE_PROMOTION_QUEUE,
    CF_CORPUS_AXIOM,
    CF_CORPUS_DOMAIN,
    CF_CORPUS_META,
    CF_REVERSE_DEPS,
];

/// Compute the RocksDB block-cache budget in bytes.
///
/// Honors `NASRUDIN_ROCKS_BLOCK_CACHE_MB` if set; otherwise reserves
/// 1 GB for everything else (Postgres `shared_buffers` ~300 MB,
/// Caddy ~20 MB, Node SSR ~250 MB, GA worker + Lean ~400 MB,
/// kernel/system ~300 MB, API process baseline excluding cache
/// ~150 MB) and gives the rest to the RocksDB block cache, clamped
/// to `[64 MB, 8 GB]`.
///
/// **Effective sizing on common instances:**
///
/// | RAM   | Cache         | % of total |
/// |-------|---------------|------------|
/// | 1 GB  | 64 MB (floor) | 6 %        |
/// | 2 GB  | 1 GB          | 50 %       |
/// | 4 GB  | 3 GB          | 75 %       |
/// | 8 GB  | 7 GB          | 87 %       |
/// | 16 GB | 8 GB (cap)    | 50 %       |
/// | 32 GB | 8 GB (cap)    | 25 %       |
///
/// The 8 GB cap exists because past that the LRU lock contention
/// and eviction overhead make the OS page cache more efficient
/// than RocksDB's own. The floor exists for tiny dev VMs.
///
/// For the Mathlib-corpus working set (290 MB total, ~5–20 k
/// entries hot during chain search), even the 1 GB sizing on a 2 GB
/// droplet caches the entire corpus block-aligned and serves >99 %
/// of GA lookups from RAM.
///
/// Returns `(cache_bytes, total_system_bytes)` — the second value is
/// `0` when the env var override is in effect or `sysinfo` couldn't
/// introspect, used only for the boot log line.
pub fn compute_block_cache_bytes() -> (usize, usize) {
    use sysinfo::System;
    if let Some(mb) = std::env::var("NASRUDIN_ROCKS_BLOCK_CACHE_MB")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
    {
        return (mb * 1024 * 1024, 0);
    }
    let mut sys = System::new();
    sys.refresh_memory();
    let total_bytes = sys.total_memory() as usize;
    if total_bytes == 0 {
        // sysinfo couldn't introspect (CI sandbox, exotic platform).
        // Fall back to a conservative 256 MB.
        return (256 * 1024 * 1024, 0);
    }
    // Reserve = max(1.5 GB, 50 % of total).
    //
    // The 1.5 GB floor covers measured non-cache services co-located on
    // the production droplet: Postgres ~300 MB shared_buffers, Caddy
    // ~20 MB, Node SSR frontend ~250 MB, the GA worker + Lean
    // toolchain ~400 MB, kernel + journald + sshd ~300 MB, and the
    // API process baseline excluding cache ~150 MB ≈ 1.42 GB. 1.5 GB
    // gives a small safety margin.
    //
    // The 50 % rule kicks in on bigger boxes (4 GB+): even when the
    // 1.5 GB floor is comfortable, we don't want cache eating more
    // than half the RAM — leaves headroom for spike loads (a
    // particularly large Lean compile, an LLM steerer call buffering
    // a big response, etc).
    //
    // Effective sizing:
    //   1 GB: 64 MB (floor; 1.5 GB > total → 0, clamped to floor)
    //   2 GB: 512 MB (25 %; 1.5 GB binds, leaves 512 MB)
    //   4 GB: 2 GB (50 %; the 50 % rule binds)
    //   8 GB: 4 GB (50 %)
    //   16 GB+: 8 GB (cap)
    //
    // Override via `NASRUDIN_ROCKS_BLOCK_CACHE_MB`.
    const ABSOLUTE_RESERVE_MIN: usize = 1_500 * 1024 * 1024;
    let reserved = std::cmp::max(ABSOLUTE_RESERVE_MIN, total_bytes / 2);
    let avail = total_bytes.saturating_sub(reserved);
    let clamped = avail.clamp(64 * 1024 * 1024, 8 * 1024 * 1024 * 1024);
    (clamped, total_bytes)
}

/// Database statistics.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DbStats {
    pub total_theorems: u64,
    pub total_verified: u64,
    pub total_rejected: u64,
    pub total_pending: u64,
    pub total_axioms: u64,
    pub max_depth: u32,
    pub max_generation: u64,
    pub domain_counts: HashMap<String, u64>,
}

/// A pending reverification job persisted in the `reverify_queue` CF.
///
/// The async drain loop reads these jobs after a server restart and runs the
/// A→B verification cascade, then calls [`TheoremDb::dequeue_reverify`] on
/// success or updates `attempts` on retry.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReverifyJob {
    pub theorem_id: TheoremId,
    pub attempts: u8,
    pub enqueued_at_micros: i64,
}

/// Lineage record for a theorem — who are its parents, children, and axiom roots.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LineageRecord {
    pub theorem_id: TheoremId,
    pub parents: Vec<TheoremId>,
    pub children: Vec<TheoremId>,
    pub axiom_ancestors: Vec<TheoremId>,
}

/// RocksDB-backed theorem database.
pub struct TheoremDb {
    db: std::sync::Arc<DB>,
}

impl TheoremDb {
    /// Open or create a theorem database at the given path.
    ///
    /// Allocates a single shared LRU block cache (sized via
    /// [`compute_block_cache_bytes`]) and applies it to every column
    /// family. Hot pages of any kind compete for the same RAM budget,
    /// which is ideal under load: chain-search lookups (corpus-axiom
    /// reads) and theorem reads (theorem CF) share the cache instead of
    /// duplicating a tiny per-CF default.
    pub fn new(path: &str) -> Result<Self> {
        let mut db_opts = Options::default();
        db_opts.create_if_missing(true);
        db_opts.create_missing_column_families(true);

        let (cache_bytes, total_bytes) = compute_block_cache_bytes();
        let block_cache = Cache::new_lru_cache(cache_bytes);
        if total_bytes > 0 {
            tracing::info!(
                "RocksDB block cache: {} MB ({}% of {} MB system RAM)",
                cache_bytes / (1024 * 1024),
                cache_bytes * 100 / total_bytes,
                total_bytes / (1024 * 1024),
            );
        } else {
            tracing::info!(
                "RocksDB block cache: {} MB (env override / fallback)",
                cache_bytes / (1024 * 1024),
            );
        }

        // Point-lookup CFs benefit from Bloom filters to avoid unnecessary
        // disk reads for non-existent keys.
        const POINT_LOOKUP_CFS: &[&str] =
            &[CF_THEOREMS, CF_PROOFS, CF_LINEAGE, CF_REVERIFY_QUEUE, CF_ATTEMPTS, CF_TACTIC_PRIORS];

        let cf_descriptors: Vec<ColumnFamilyDescriptor> = ALL_CFS
            .iter()
            .map(|name| build_cf_descriptor(name, &block_cache, POINT_LOOKUP_CFS))
            .collect();

        let db = DB::open_cf_descriptors(&db_opts, path, cf_descriptors)
            .context("Failed to open RocksDB")?;

        Ok(Self {
            db: std::sync::Arc::new(db),
        })
    }

    /// Borrowed clone of the underlying RocksDB handle. Used by cache
    /// wrappers (`AttemptsCache::on_existing_db`,
    /// `TacticPriorsCache::on_existing_db`) to share the engine's main
    /// DB instance instead of opening a second standalone database.
    pub fn shared_db(&self) -> std::sync::Arc<DB> {
        std::sync::Arc::clone(&self.db)
    }

    // ── Theorem CRUD ──────────────────────────────────────────────────

    /// Compute the transitive axiom-ancestor closure for a theorem.
    ///
    /// Walks `theorem.proof` to collect the immediate `Axiom(id)` leaves,
    /// then unions in the cached `axiom_ancestors` of each leaf already
    /// stored in `CF_LINEAGE`. Result is deterministic (`BTreeSet`-sorted
    /// before collection) and includes every axiom transitively used by
    /// the proof. Self-references at the proof root (an axiom seed
    /// theorem whose proof is `ProofTree::Axiom(self.id)`) are stripped.
    ///
    /// Builds bottom-up: every parent's own ancestors must already be
    /// stored in CF_LINEAGE. The backfill task is responsible for
    /// populating in topological order; on the live write path,
    /// `put_theorem` orders writes such that parents land first.
    fn compute_transitive_ancestors(
        &self,
        theorem: &nasrudin_core::Theorem,
    ) -> Result<Vec<nasrudin_core::TheoremId>> {
        let mut acc: std::collections::BTreeSet<nasrudin_core::TheoremId> =
            nasrudin_core::collect_axiom_ids(&theorem.proof);
        let immediate: Vec<_> = acc.iter().copied().collect();
        for parent_id in &immediate {
            if parent_id == &theorem.id {
                continue;
            }
            if let Some(parent_lineage) = self.get_lineage(parent_id)? {
                for a in parent_lineage.axiom_ancestors {
                    acc.insert(a);
                }
            }
        }
        acc.remove(&theorem.id);
        Ok(acc.into_iter().collect())
    }

    /// Store a theorem and update all secondary indexes + stats atomically.
    pub fn put_theorem(&self, theorem: &Theorem) -> Result<()> {
        let mut batch = WriteBatch::default();

        // Main theorem record
        let cf_theorems = self
            .db
            .cf_handle(CF_THEOREMS)
            .context("Missing theorems CF")?;
        let value = serde_json::to_vec(theorem).context("Failed to serialize theorem")?;
        batch.put_cf(&cf_theorems, theorem.id, &value);

        // Proof record
        let cf_proofs = self
            .db
            .cf_handle(CF_PROOFS)
            .context("Missing proofs CF")?;
        let proof_value =
            serde_json::to_vec(&theorem.proof).context("Failed to serialize proof")?;
        batch.put_cf(&cf_proofs, theorem.id, &proof_value);

        // Lineage record (transitive ancestor closure)
        let cf_lineage = self
            .db
            .cf_handle(CF_LINEAGE)
            .context("Missing lineage CF")?;
        let ancestors = self.compute_transitive_ancestors(theorem)?;
        let lineage = LineageRecord {
            theorem_id: theorem.id,
            parents: theorem.parents.clone(),
            children: theorem.children.clone(),
            axiom_ancestors: ancestors.clone(),
        };
        let lineage_value =
            serde_json::to_vec(&lineage).context("Failed to serialize lineage")?;
        batch.put_cf(&cf_lineage, theorem.id, &lineage_value);

        // Reverse-deps index — one row per (ancestor, theorem) edge so
        // `forbidden_for_target` can answer "what depends on X?" with a
        // single prefix scan instead of walking every proof tree.
        let cf_reverse = self
            .db
            .cf_handle(CF_REVERSE_DEPS)
            .context("Missing reverse_deps CF")?;
        for ancestor_id in &ancestors {
            let mut key = [0u8; 16];
            key[..8].copy_from_slice(ancestor_id);
            key[8..].copy_from_slice(&theorem.id);
            batch.put_cf(&cf_reverse, key, &[] as &[u8]);
        }

        // Domain index
        let cf_domain = self
            .db
            .cf_handle(CF_BY_DOMAIN)
            .context("Missing by_domain CF")?;
        let domain_str = domain_to_key(&theorem.domain);
        let domain_key = format!("{}:{}", domain_str, hex::encode(theorem.id));
        batch.put_cf(&cf_domain, domain_key.as_bytes(), theorem.id);

        // Depth index
        let cf_depth = self
            .db
            .cf_handle(CF_BY_DEPTH)
            .context("Missing by_depth CF")?;
        let depth_key = format!("{:010}:{}", theorem.depth, hex::encode(theorem.id));
        batch.put_cf(&cf_depth, depth_key.as_bytes(), theorem.id);

        // Generation index
        let cf_gen = self
            .db
            .cf_handle(CF_BY_GENERATION)
            .context("Missing by_generation CF")?;
        let gen_key = format!("{:020}:{}", theorem.generation, hex::encode(theorem.id));
        batch.put_cf(&cf_gen, gen_key.as_bytes(), theorem.id);

        // LaTeX index
        if !theorem.latex.is_empty() {
            let cf_latex = self
                .db
                .cf_handle(CF_LATEX_INDEX)
                .context("Missing latex_index CF")?;
            let normalized: String = theorem.latex.chars().filter(|c| !c.is_whitespace()).collect();
            batch.put_cf(&cf_latex, normalized.as_bytes(), theorem.id);
        }

        // Axiom index — index each parent so we can query "all theorems derived from axiom X"
        let cf_axiom = self
            .db
            .cf_handle(CF_BY_AXIOM)
            .context("Missing by_axiom CF")?;
        for parent_id in &theorem.parents {
            let axiom_key = format!("{}:{}", hex::encode(parent_id), hex::encode(theorem.id));
            batch.put_cf(&cf_axiom, axiom_key.as_bytes(), theorem.id);
        }

        // Commit the batch atomically
        self.db
            .write(batch)
            .context("Failed to write theorem batch")?;

        // Update stats (separate write — stats are best-effort)
        self.increment_stats(theorem)?;

        Ok(())
    }

    /// Retrieve a theorem by its ID.
    pub fn get_theorem(&self, id: &TheoremId) -> Result<Option<Theorem>> {
        let cf = self
            .db
            .cf_handle(CF_THEOREMS)
            .context("Missing theorems CF")?;
        match self.db.get_cf(&cf, id).context("Failed to get theorem")? {
            Some(bytes) => {
                let theorem: Theorem =
                    serde_json::from_slice(&bytes).context("Failed to deserialize theorem")?;
                Ok(Some(theorem))
            }
            None => Ok(None),
        }
    }

    /// Check whether a theorem exists in the database.
    pub fn theorem_exists(&self, id: &TheoremId) -> Result<bool> {
        let cf = self
            .db
            .cf_handle(CF_THEOREMS)
            .context("Missing theorems CF")?;
        let exists = self
            .db
            .get_cf(&cf, id)
            .context("Failed to check theorem")?
            .is_some();
        Ok(exists)
    }

    /// List all theorems in the database.
    pub fn list_theorems(&self) -> Result<Vec<Theorem>> {
        let cf = self
            .db
            .cf_handle(CF_THEOREMS)
            .context("Missing theorems CF")?;
        let mut theorems = Vec::new();
        let iter = self.db.iterator_cf(&cf, IteratorMode::Start);
        for item in iter {
            let (_, value) = item.context("Failed to iterate theorems")?;
            let theorem: Theorem =
                serde_json::from_slice(&value).context("Failed to deserialize theorem")?;
            theorems.push(theorem);
        }
        Ok(theorems)
    }

    // ── Proof Storage ─────────────────────────────────────────────────

    /// Store a proof tree for a theorem.
    pub fn put_proof(&self, theorem_id: &TheoremId, proof: &ProofTree) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_PROOFS)
            .context("Missing proofs CF")?;
        let value = serde_json::to_vec(proof).context("Failed to serialize proof")?;
        self.db
            .put_cf(&cf, theorem_id, &value)
            .context("Failed to put proof")?;
        Ok(())
    }

    /// Retrieve a proof tree by theorem ID.
    pub fn get_proof(&self, theorem_id: &TheoremId) -> Result<Option<ProofTree>> {
        let cf = self
            .db
            .cf_handle(CF_PROOFS)
            .context("Missing proofs CF")?;
        match self
            .db
            .get_cf(&cf, theorem_id)
            .context("Failed to get proof")?
        {
            Some(bytes) => {
                let proof: ProofTree =
                    serde_json::from_slice(&bytes).context("Failed to deserialize proof")?;
                Ok(Some(proof))
            }
            None => Ok(None),
        }
    }

    // ── Lineage Storage ───────────────────────────────────────────────

    /// Store a lineage record for a theorem.
    pub fn put_lineage(&self, lineage: &LineageRecord) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_LINEAGE)
            .context("Missing lineage CF")?;
        let value = serde_json::to_vec(lineage).context("Failed to serialize lineage")?;
        self.db
            .put_cf(&cf, lineage.theorem_id, &value)
            .context("Failed to put lineage")?;
        Ok(())
    }

    /// Retrieve a lineage record by theorem ID.
    pub fn get_lineage(&self, theorem_id: &TheoremId) -> Result<Option<LineageRecord>> {
        let cf = self
            .db
            .cf_handle(CF_LINEAGE)
            .context("Missing lineage CF")?;
        match self
            .db
            .get_cf(&cf, theorem_id)
            .context("Failed to get lineage")?
        {
            Some(bytes) => {
                let lineage: LineageRecord =
                    serde_json::from_slice(&bytes).context("Failed to deserialize lineage")?;
                Ok(Some(lineage))
            }
            None => Ok(None),
        }
    }

    // ── Secondary Index Queries ─────────────────────────────────────────

    /// List theorem IDs for a given domain, up to `limit` results (0 = unlimited).
    pub fn list_by_domain_limit(&self, domain: &Domain, limit: usize) -> Result<Vec<TheoremId>> {
        let cf = self
            .db
            .cf_handle(CF_BY_DOMAIN)
            .context("Missing by_domain CF")?;
        let prefix = format!("{}:", domain_to_key(domain));
        let mut ids = Vec::new();
        let iter = self
            .db
            .prefix_iterator_cf(&cf, prefix.as_bytes());
        for item in iter {
            let (key, value) = item.context("Failed to iterate by_domain")?;
            if !key.starts_with(prefix.as_bytes()) {
                break;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&value[..8]);
            ids.push(id);
            if limit > 0 && ids.len() >= limit {
                break;
            }
        }
        Ok(ids)
    }

    /// List all theorem IDs for a given domain.
    pub fn list_by_domain(&self, domain: &Domain) -> Result<Vec<TheoremId>> {
        self.list_by_domain_limit(domain, 0)
    }

    // ── Stats ─────────────────────────────────────────────────────────

    /// Get database statistics.
    pub fn get_stats(&self) -> Result<DbStats> {
        let cf = self.db.cf_handle(CF_STATS).context("Missing stats CF")?;
        match self
            .db
            .get_cf(&cf, b"global")
            .context("Failed to get stats")?
        {
            Some(bytes) => {
                // Handle corrupt/stale stats gracefully by resetting to default
                match serde_json::from_slice::<DbStats>(&bytes) {
                    Ok(stats) => Ok(stats),
                    Err(e) => {
                        tracing::warn!("Stats deserialization failed ({e}), resetting to default");
                        let default = DbStats::default();
                        // Overwrite corrupt data
                        let _ = self.put_stats(&default);
                        Ok(default)
                    }
                }
            }
            None => Ok(DbStats::default()),
        }
    }

    /// Persist stats to the stats CF.
    fn put_stats(&self, stats: &DbStats) -> Result<()> {
        let cf = self.db.cf_handle(CF_STATS).context("Missing stats CF")?;
        let value = serde_json::to_vec(stats).context("Failed to serialize stats")?;
        self.db
            .put_cf(&cf, b"global", &value)
            .context("Failed to put stats")?;
        Ok(())
    }

    /// Increment stats based on a newly stored theorem.
    fn increment_stats(&self, theorem: &Theorem) -> Result<()> {
        let mut stats = self.get_stats()?;
        stats.total_theorems += 1;

        match &theorem.verified {
            VerificationStatus::Verified { .. } => stats.total_verified += 1,
            VerificationStatus::Rejected { .. } => stats.total_rejected += 1,
            VerificationStatus::Pending => stats.total_pending += 1,
            VerificationStatus::Timeout => stats.total_pending += 1,
        }

        if matches!(&theorem.origin, nasrudin_core::TheoremOrigin::Axiom) {
            stats.total_axioms += 1;
        }

        if theorem.depth > stats.max_depth {
            stats.max_depth = theorem.depth;
        }
        if theorem.generation > stats.max_generation {
            stats.max_generation = theorem.generation;
        }

        // Track per-domain counts
        let domain_key = domain_to_key(&theorem.domain);
        *stats.domain_counts.entry(domain_key).or_insert(0) += 1;

        self.put_stats(&stats)?;
        Ok(())
    }

    // ── Query Methods ──────────────────────────────────────────────────

    /// List theorem IDs at a given derivation depth, up to `limit` (0 = unlimited).
    pub fn list_by_depth_limit(&self, depth: u32, limit: usize) -> Result<Vec<TheoremId>> {
        let cf = self
            .db
            .cf_handle(CF_BY_DEPTH)
            .context("Missing by_depth CF")?;
        let prefix = format!("{:010}:", depth);
        let mut ids = Vec::new();
        let iter = self.db.prefix_iterator_cf(&cf, prefix.as_bytes());
        for item in iter {
            let (key, value) = item.context("Failed to iterate by_depth")?;
            if !key.starts_with(prefix.as_bytes()) {
                break;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&value[..8]);
            ids.push(id);
            if limit > 0 && ids.len() >= limit {
                break;
            }
        }
        Ok(ids)
    }

    /// List all theorem IDs at a given derivation depth.
    pub fn list_by_depth(&self, depth: u32) -> Result<Vec<TheoremId>> {
        self.list_by_depth_limit(depth, 0)
    }

    /// List theorem IDs from a given generation, up to `limit` (0 = unlimited).
    pub fn list_by_generation_limit(&self, generation: u64, limit: usize) -> Result<Vec<TheoremId>> {
        let cf = self
            .db
            .cf_handle(CF_BY_GENERATION)
            .context("Missing by_generation CF")?;
        let prefix = format!("{:020}:", generation);
        let mut ids = Vec::new();
        let iter = self.db.prefix_iterator_cf(&cf, prefix.as_bytes());
        for item in iter {
            let (key, value) = item.context("Failed to iterate by_generation")?;
            if !key.starts_with(prefix.as_bytes()) {
                break;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&value[..8]);
            ids.push(id);
            if limit > 0 && ids.len() >= limit {
                break;
            }
        }
        Ok(ids)
    }

    /// List all theorem IDs from a given generation.
    pub fn list_by_generation(&self, generation: u64) -> Result<Vec<TheoremId>> {
        self.list_by_generation_limit(generation, 0)
    }

    /// List theorem IDs derived from a given parent/axiom, up to `limit` (0 = unlimited).
    pub fn list_by_axiom_limit(&self, axiom_id: &TheoremId, limit: usize) -> Result<Vec<TheoremId>> {
        let cf = self
            .db
            .cf_handle(CF_BY_AXIOM)
            .context("Missing by_axiom CF")?;
        let prefix = format!("{}:", hex::encode(axiom_id));
        let mut ids = Vec::new();
        let iter = self.db.prefix_iterator_cf(&cf, prefix.as_bytes());
        for item in iter {
            let (key, value) = item.context("Failed to iterate by_axiom")?;
            if !key.starts_with(prefix.as_bytes()) {
                break;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&value[..8]);
            ids.push(id);
            if limit > 0 && ids.len() >= limit {
                break;
            }
        }
        Ok(ids)
    }

    /// List all theorem IDs derived from a given parent/axiom.
    pub fn list_by_axiom(&self, axiom_id: &TheoremId) -> Result<Vec<TheoremId>> {
        self.list_by_axiom_limit(axiom_id, 0)
    }

    /// List every theorem whose proof transitively cites `ancestor_id`.
    ///
    /// Prefix-scans `CF_REVERSE_DEPS` on the 8-byte `ancestor_id`. The
    /// values are ignored; the dependent id is the second half of the
    /// 16-byte key. Returns deterministic order (RocksDB iterator order
    /// over the lex-sorted dependent ids).
    pub fn list_dependents(&self, ancestor_id: &TheoremId) -> Result<Vec<TheoremId>> {
        let cf = self
            .db
            .cf_handle(CF_REVERSE_DEPS)
            .context("Missing reverse_deps CF")?;
        let mut out = Vec::new();
        let iter = self.db.prefix_iterator_cf(&cf, ancestor_id);
        for item in iter {
            let (key, _) = item.context("Failed to iterate reverse_deps")?;
            if key.len() != 16 || !key.starts_with(ancestor_id) {
                break;
            }
            let mut dep = [0u8; 8];
            dep.copy_from_slice(&key[8..16]);
            out.push(dep);
        }
        Ok(out)
    }

    /// Prefix search on the LaTeX index, up to `limit` results (0 = unlimited).
    pub fn search_latex_limit(&self, prefix: &str, limit: usize) -> Result<Vec<TheoremId>> {
        let cf = self
            .db
            .cf_handle(CF_LATEX_INDEX)
            .context("Missing latex_index CF")?;
        let normalized: String = prefix.chars().filter(|c| !c.is_whitespace()).collect();
        let mut ids = Vec::new();
        let iter = self
            .db
            .prefix_iterator_cf(&cf, normalized.as_bytes());
        for item in iter {
            let (key, value) = item.context("Failed to iterate latex_index")?;
            if !key.starts_with(normalized.as_bytes()) {
                break;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&value[..8]);
            ids.push(id);
            if limit > 0 && ids.len() >= limit {
                break;
            }
        }
        Ok(ids)
    }

    /// Prefix search on the LaTeX index (unlimited).
    pub fn search_latex(&self, prefix: &str) -> Result<Vec<TheoremId>> {
        self.search_latex_limit(prefix, 0)
    }

    /// List the most recent theorems by generation (descending), up to `limit`.
    pub fn list_recent(&self, limit: usize) -> Result<Vec<Theorem>> {
        let cf = self
            .db
            .cf_handle(CF_BY_GENERATION)
            .context("Missing by_generation CF")?;
        let mut recent_ids = Vec::new();
        let iter = self.db.iterator_cf(&cf, IteratorMode::End);
        for item in iter {
            let (_, value) = item.context("Failed to iterate by_generation")?;
            let mut id = [0u8; 8];
            id.copy_from_slice(&value[..8]);
            recent_ids.push(id);
            if recent_ids.len() >= limit {
                break;
            }
        }
        let mut theorems = Vec::with_capacity(recent_ids.len());
        for id in &recent_ids {
            match self.get_theorem(id) {
                Ok(Some(thm)) => theorems.push(thm),
                Ok(None) => {} // index points to deleted record — skip
                Err(e) => {
                    tracing::warn!("Skipping corrupt theorem {}: {e}", hex::encode(id));
                }
            }
        }
        Ok(theorems)
    }

    /// Count theorems per domain using the pre-computed stats.
    pub fn count_by_domain(&self) -> Result<HashMap<String, u64>> {
        let stats = self.get_stats()?;
        Ok(stats.domain_counts)
    }

    /// Delete a theorem and all its index entries.
    pub fn delete_theorem(&self, id: &TheoremId) -> Result<()> {
        // Read the theorem first to know what indexes to clean up
        let theorem = match self.get_theorem(id)? {
            Some(t) => t,
            None => return Ok(()),
        };

        let mut batch = WriteBatch::default();

        // Main record
        let cf_theorems = self
            .db
            .cf_handle(CF_THEOREMS)
            .context("Missing theorems CF")?;
        batch.delete_cf(&cf_theorems, id);

        // Proof
        let cf_proofs = self
            .db
            .cf_handle(CF_PROOFS)
            .context("Missing proofs CF")?;
        batch.delete_cf(&cf_proofs, id);

        // Lineage
        let cf_lineage = self
            .db
            .cf_handle(CF_LINEAGE)
            .context("Missing lineage CF")?;
        batch.delete_cf(&cf_lineage, id);

        // Domain index
        let cf_domain = self
            .db
            .cf_handle(CF_BY_DOMAIN)
            .context("Missing by_domain CF")?;
        let domain_key = format!("{}:{}", domain_to_key(&theorem.domain), hex::encode(id));
        batch.delete_cf(&cf_domain, domain_key.as_bytes());

        // Depth index
        let cf_depth = self
            .db
            .cf_handle(CF_BY_DEPTH)
            .context("Missing by_depth CF")?;
        let depth_key = format!("{:010}:{}", theorem.depth, hex::encode(id));
        batch.delete_cf(&cf_depth, depth_key.as_bytes());

        // Generation index
        let cf_gen = self
            .db
            .cf_handle(CF_BY_GENERATION)
            .context("Missing by_generation CF")?;
        let gen_key = format!("{:020}:{}", theorem.generation, hex::encode(id));
        batch.delete_cf(&cf_gen, gen_key.as_bytes());

        // LaTeX index
        if !theorem.latex.is_empty() {
            let cf_latex = self
                .db
                .cf_handle(CF_LATEX_INDEX)
                .context("Missing latex_index CF")?;
            let normalized: String = theorem.latex.chars().filter(|c| !c.is_whitespace()).collect();
            batch.delete_cf(&cf_latex, normalized.as_bytes());
        }

        // Axiom index entries
        let cf_axiom = self
            .db
            .cf_handle(CF_BY_AXIOM)
            .context("Missing by_axiom CF")?;
        for parent_id in &theorem.parents {
            let axiom_key = format!("{}:{}", hex::encode(parent_id), hex::encode(id));
            batch.delete_cf(&cf_axiom, axiom_key.as_bytes());
        }

        self.db
            .write(batch)
            .context("Failed to delete theorem batch")?;

        Ok(())
    }

    /// Append a child to a theorem's lineage record.
    pub fn add_child(&self, parent_id: &TheoremId, child_id: TheoremId) -> Result<()> {
        let mut lineage = self
            .get_lineage(parent_id)?
            .unwrap_or(LineageRecord {
                theorem_id: *parent_id,
                parents: vec![],
                children: vec![],
                axiom_ancestors: vec![],
            });
        if !lineage.children.contains(&child_id) {
            lineage.children.push(child_id);
        }
        self.put_lineage(&lineage)?;
        Ok(())
    }

    // ── Reverify Queue ────────────────────────────────────────────────

    /// Insert (or overwrite) a pending reverification job keyed by `theorem_id`.
    pub fn enqueue_reverify(&self, job: &ReverifyJob) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_REVERIFY_QUEUE)
            .context("Missing reverify_queue CF")?;
        let value = serde_json::to_vec(job).context("Failed to serialize ReverifyJob")?;
        self.db
            .put_cf(&cf, job.theorem_id, &value)
            .context("Failed to enqueue reverify job")?;
        Ok(())
    }

    /// Remove a reverification job for the given `theorem_id`.
    pub fn dequeue_reverify(&self, theorem_id: &TheoremId) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_REVERIFY_QUEUE)
            .context("Missing reverify_queue CF")?;
        self.db
            .delete_cf(&cf, theorem_id)
            .context("Failed to dequeue reverify job")?;
        Ok(())
    }

    /// List up to `limit` pending reverification jobs (in iterator order).
    /// Pass `limit = 0` for unlimited (matches the convention used by
    /// `list_by_domain_limit`, `list_by_depth_limit`, etc.).
    pub fn list_reverify_pending(&self, limit: usize) -> Result<Vec<ReverifyJob>> {
        let cf = self
            .db
            .cf_handle(CF_REVERIFY_QUEUE)
            .context("Missing reverify_queue CF")?;
        let mut out = Vec::new();
        for item in self.db.iterator_cf(&cf, IteratorMode::Start) {
            let (_, v) = item.context("Failed to iterate reverify_queue")?;
            out.push(serde_json::from_slice(&v).context("Failed to deserialize ReverifyJob")?);
            if limit > 0 && out.len() >= limit {
                break;
            }
        }
        Ok(out)
    }

    /// Total number of jobs currently in the reverify queue.
    pub fn reverify_queue_depth(&self) -> Result<usize> {
        let cf = self
            .db
            .cf_handle(CF_REVERIFY_QUEUE)
            .context("Missing reverify_queue CF")?;
        Ok(self.db.iterator_cf(&cf, IteratorMode::Start).count())
    }

    // ── PG-insert Queue (write-behind) ────────────────────────────────

    /// Enqueue a payload (typically a bincode-serialised
    /// `nasrudin_pg::query::theorems::NewTheorem`) for asynchronous
    /// PG insertion. Keyed by theorem_id. Idempotent — re-enqueueing
    /// the same id overwrites the existing payload (which is fine,
    /// since PG insert is itself idempotent on the `(canonical_hash)`
    /// unique constraint).
    pub fn enqueue_pg_insert(&self, theorem_id: &TheoremId, payload: &[u8]) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_PG_INSERT_QUEUE)
            .context("Missing pg_insert_queue CF")?;
        self.db
            .put_cf(&cf, theorem_id, payload)
            .context("enqueue pg_insert")?;
        Ok(())
    }

    /// Drain up to `batch_size` pending PG-insert payloads. Returns
    /// `(theorem_id, payload)` pairs in iterator order. Caller is
    /// expected to insert each into PG, then call
    /// [`Self::ack_pg_insert`] on success. On insert failure the row
    /// stays in the queue and is retried on the next drain tick.
    pub fn drain_pg_insert_queue(
        &self,
        batch_size: usize,
    ) -> Result<Vec<(TheoremId, Vec<u8>)>> {
        let cf = self
            .db
            .cf_handle(CF_PG_INSERT_QUEUE)
            .context("Missing pg_insert_queue CF")?;
        let mut out = Vec::new();
        for item in self.db.iterator_cf(&cf, IteratorMode::Start) {
            let (k, v) = item.context("iter pg_insert_queue")?;
            if k.len() != 8 {
                continue;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&k);
            out.push((id, v.to_vec()));
            if out.len() >= batch_size {
                break;
            }
        }
        Ok(out)
    }

    /// Acknowledge a PG insert succeeded — removes the payload from the
    /// queue. Subsequent boots won't re-attempt it.
    pub fn ack_pg_insert(&self, theorem_id: &TheoremId) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_PG_INSERT_QUEUE)
            .context("Missing pg_insert_queue CF")?;
        self.db
            .delete_cf(&cf, theorem_id)
            .context("ack pg_insert")?;
        Ok(())
    }

    /// Number of theorems queued for PG insertion. Exposed for `/api/health`.
    pub fn pg_insert_queue_depth(&self) -> Result<usize> {
        let cf = self
            .db
            .cf_handle(CF_PG_INSERT_QUEUE)
            .context("Missing pg_insert_queue CF")?;
        Ok(self.db.iterator_cf(&cf, IteratorMode::Start).count())
    }

    // ── Cascade Rejection (P-Task 3) ──────────────────────────────────

    /// BFS-walk the lineage graph starting from `root_id` and mark
    /// every visited theorem as `Rejected`. Used by the lake-promotion
    /// drain when lake build rejects a theorem — every descendant in
    /// `CF_LINEAGE` that was built on top of the now-bogus theorem
    /// must also be invalidated, otherwise the corpus accumulates
    /// poisoned chains forever.
    ///
    /// Returns the full set of invalidated theorem_ids (including
    /// `root_id`) so the caller can broadcast SSE `TheoremRejected`
    /// events and propagate to PG via `mark_rejected_batch`.
    ///
    /// Bounded scan: in pathological cases (a foundational theorem
    /// with thousands of descendants) this can take seconds. Callers
    /// should run it in `tokio::task::spawn_blocking` to keep the
    /// async runtime responsive.
    pub fn cascade_reject(
        &self,
        root_id: TheoremId,
        reason: &str,
    ) -> Result<Vec<TheoremId>> {
        use std::collections::{HashSet, VecDeque};
        let mut visited: HashSet<TheoremId> = HashSet::new();
        let mut queue: VecDeque<TheoremId> = VecDeque::new();
        let mut invalidated: Vec<TheoremId> = Vec::new();
        queue.push_back(root_id);
        visited.insert(root_id);

        while let Some(node) = queue.pop_front() {
            // Mutate the theorem's status. For the root, use the
            // caller-provided reason verbatim. For descendants, use
            // a uniform "ancestor_rejected: <root_hex>" reason.
            let local_reason = if node == root_id {
                reason.to_string()
            } else {
                format!("ancestor_rejected: {}", hex::encode(root_id))
            };
            if let Some(mut theorem) = self.get_theorem(&node)? {
                theorem.verified = nasrudin_core::VerificationStatus::Rejected {
                    reason: local_reason,
                };
                // put_theorem atomically updates CF_THEOREMS + every
                // secondary index (including CF_BY_VERIFIED_AT, which
                // entry should already be absent for a Rejected row,
                // but put_theorem only writes the index when status
                // matches Verified — see the existing impl).
                self.put_theorem(&theorem).ok();
            }
            invalidated.push(node);

            // Enqueue children from CF_LINEAGE.
            if let Ok(Some(lineage)) = self.get_lineage(&node) {
                for child in lineage.children {
                    if visited.insert(child) {
                        queue.push_back(child);
                    }
                }
            }

            // Bounded progress logging — every 500 nodes — so a runaway
            // cascade is observable.
            if invalidated.len() % 500 == 0 {
                tracing::info!(
                    cascade_root = %hex::encode(root_id),
                    invalidated_so_far = invalidated.len(),
                    "cascade_reject: progress"
                );
            }
        }

        if invalidated.len() > 1 {
            tracing::warn!(
                cascade_root = %hex::encode(root_id),
                total_invalidated = invalidated.len(),
                descendants = invalidated.len() - 1,
                "cascade_reject: complete"
            );
        }

        Ok(invalidated)
    }

    // ── Lake-Promotion Queue (P-Task 2) ───────────────────────────────

    /// Enqueue a theorem for asynchronous lake-build promotion. Priority
    /// lanes: 0 = manual/sync, 1 = seed-inclusion demand, 2 = background
    /// crawler. Idempotent: re-enqueueing the same theorem at the same
    /// priority is a no-op (overwrites with the same key); re-enqueueing
    /// at a *higher* priority adds a new row that will be drained first.
    /// On promotion success/failure the drain calls
    /// [`Self::ack_lake_promotion`] for every queued row keyed by this
    /// theorem_id (across all priorities).
    pub fn enqueue_lake_promotion(
        &self,
        theorem_id: &TheoremId,
        priority: u8,
    ) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_LAKE_PROMOTION_QUEUE)
            .context("Missing lake_promotion_queue CF")?;
        let now_micros = chrono::Utc::now().timestamp_micros() as u64;
        let mut key = Vec::with_capacity(17);
        key.push(priority);
        key.extend_from_slice(&now_micros.to_be_bytes());
        key.extend_from_slice(theorem_id);
        // Empty value — the key contains everything.
        self.db
            .put_cf(&cf, &key, &[])
            .context("enqueue lake_promotion")?;
        Ok(())
    }

    /// Drain up to `batch_size` queued lake-promotion entries in
    /// priority-then-FIFO order. Returns the queue keys (so callers can
    /// ack them precisely) and the theorem_ids extracted from each.
    pub fn drain_lake_promotion_batch(
        &self,
        batch_size: usize,
    ) -> Result<Vec<(Vec<u8>, TheoremId)>> {
        let cf = self
            .db
            .cf_handle(CF_LAKE_PROMOTION_QUEUE)
            .context("Missing lake_promotion_queue CF")?;
        let mut out = Vec::new();
        for item in self.db.iterator_cf(&cf, IteratorMode::Start) {
            let (k, _v) = item.context("iter lake_promotion_queue")?;
            if k.len() != 17 {
                continue;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&k[9..17]);
            out.push((k.to_vec(), id));
            if out.len() >= batch_size {
                break;
            }
        }
        Ok(out)
    }

    /// Acknowledge a single queue entry by its raw key. The drain calls
    /// this on both lake-success and lake-failure outcomes so the queue
    /// drains in finite time even if the underlying theorem can't be
    /// promoted (in which case the cascade-reject machinery flips it
    /// to Rejected and we don't re-attempt).
    pub fn ack_lake_promotion(&self, key: &[u8]) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_LAKE_PROMOTION_QUEUE)
            .context("Missing lake_promotion_queue CF")?;
        self.db
            .delete_cf(&cf, key)
            .context("ack lake_promotion")?;
        Ok(())
    }

    /// Ack every queued entry for a given theorem_id (across all
    /// priority lanes). Used after a definitive outcome so a manual
    /// trigger (priority 0) doesn't re-fire if the same theorem also
    /// had a pending priority-1 or priority-2 entry.
    pub fn ack_lake_promotion_all(&self, theorem_id: &TheoremId) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_LAKE_PROMOTION_QUEUE)
            .context("Missing lake_promotion_queue CF")?;
        let mut to_delete = Vec::new();
        for item in self.db.iterator_cf(&cf, IteratorMode::Start) {
            let (k, _) = item.context("iter lake_promotion_queue")?;
            if k.len() == 17 && &k[9..17] == theorem_id {
                to_delete.push(k.to_vec());
            }
        }
        for k in to_delete {
            self.db.delete_cf(&cf, &k).ok();
        }
        Ok(())
    }

    /// Total queue depth across all priority lanes. Exposed for
    /// `/api/health` and `/api/stats` so operators can see the
    /// lake-promotion backlog.
    pub fn lake_promotion_queue_depth(&self) -> Result<usize> {
        let cf = self
            .db
            .cf_handle(CF_LAKE_PROMOTION_QUEUE)
            .context("Missing lake_promotion_queue CF")?;
        Ok(self.db.iterator_cf(&cf, IteratorMode::Start).count())
    }

    // ── Verified-At Index ─────────────────────────────────────────────

    /// Mark a theorem's verification timestamp in the recency index.
    /// Used by `/api/seed` and `/api/theorems/recent` to serve newest-
    /// first results without hitting Postgres. Atomically writes the
    /// `(timestamp_be_micros, theorem_id)` index row.
    pub fn mark_verified_at(
        &self,
        theorem_id: &TheoremId,
        verified_at_micros: i64,
    ) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_BY_VERIFIED_AT)
            .context("Missing by_verified_at CF")?;
        // Big-endian micros so lex order = chronological. Append theorem_id
        // for uniqueness on identical timestamps (rare but possible).
        let mut key = Vec::with_capacity(16);
        key.extend_from_slice(&verified_at_micros.to_be_bytes());
        key.extend_from_slice(theorem_id);
        self.db
            .put_cf(&cf, &key, theorem_id)
            .context("write verified_at index")?;
        Ok(())
    }

    /// Walk `CF_THEOREMS` and return the canonical hashes of every
    /// theorem currently in `Rejected` (or `Timeout`) status. Used by
    /// `/api/rejected_hashes` so peer workers can short-circuit chains
    /// that the cluster has already lake-rejected. `limit = 0` means
    /// unbounded.
    pub fn list_rejected_canonical_hashes(&self, limit: usize) -> Result<Vec<TheoremId>> {
        let cf = self
            .db
            .cf_handle(CF_THEOREMS)
            .context("Missing theorems CF")?;
        let mut out = Vec::new();
        for item in self.db.iterator_cf(&cf, IteratorMode::Start) {
            let (k, v) = item.context("iter theorems")?;
            if k.len() != 8 {
                continue;
            }
            let theorem: Theorem = match serde_json::from_slice(&v) {
                Ok(t) => t,
                Err(_) => continue,
            };
            let rejected = matches!(
                theorem.verified,
                nasrudin_core::VerificationStatus::Rejected { .. }
                    | nasrudin_core::VerificationStatus::Timeout
            );
            if rejected {
                let mut id = [0u8; 8];
                id.copy_from_slice(&k);
                out.push(id);
                if limit > 0 && out.len() >= limit {
                    break;
                }
            }
        }
        Ok(out)
    }

    /// Iterate the verified-at index in newest-first order, returning
    /// up to `top` theorem_ids. Optionally filtered by domain (the
    /// caller looks up each Theorem and rejects if the domain doesn't
    /// match — cheaper than maintaining a per-domain index for the
    /// modest seed-query top sizes).
    pub fn list_verified_recent_ids(&self, top: usize) -> Result<Vec<TheoremId>> {
        let cf = self
            .db
            .cf_handle(CF_BY_VERIFIED_AT)
            .context("Missing by_verified_at CF")?;
        let mut out = Vec::new();
        for item in self.db.iterator_cf(&cf, IteratorMode::End) {
            let (_, v) = item.context("iter by_verified_at")?;
            if v.len() != 8 {
                continue;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&v);
            out.push(id);
            if out.len() >= top {
                break;
            }
        }
        Ok(out)
    }

    // ── Dump (for debugging) ──────────────────────────────────────────

    /// Dump all column family contents for debugging.
    pub fn dump_all(&self) -> Result<()> {
        for cf_name in ALL_CFS {
            let cf = self
                .db
                .cf_handle(cf_name)
                .context(format!("Missing {cf_name} CF"))?;
            let count = self.db.iterator_cf(&cf, IteratorMode::Start).count();
            println!("  CF '{cf_name}': {count} entries");
        }
        Ok(())
    }
}

/// Build a `ColumnFamilyDescriptor` with per-CF tuning. Routes:
///
/// - `CF_CORPUS_AXIOM` → bloom filter + `optimize_for_point_lookup` so
///   chain-engine name lookups hit the bloom filter on misses
///   (RAM-speed) and the block cache on hits.
/// - `CF_CORPUS_DOMAIN` → default block-based table; this CF is
///   range-scanned, not point-looked-up, so bloom filters would just
///   waste cache slots.
/// - Other point-lookup CFs (theorems, proofs, etc.) → bloom filter
///   only (their working set is small so they don't need the
///   point-lookup optimization).
/// - All CFs share the global LRU block cache.
fn build_cf_descriptor(
    name: &str,
    block_cache: &Cache,
    point_lookup_cfs: &[&str],
) -> ColumnFamilyDescriptor {
    let mut cf_opts = Options::default();
    let mut block_opts = BlockBasedOptions::default();
    block_opts.set_block_cache(block_cache);
    if name == CF_CORPUS_AXIOM {
        // 10 bits/key bloom — negative lookups (axiom not in corpus,
        // common for hand-coded postulate names that only live in the
        // hot tier) become RAM-speed without a disk seek.
        block_opts.set_bloom_filter(10.0, false);
        block_opts.set_whole_key_filtering(true);
        cf_opts.set_block_based_table_factory(&block_opts);
        // 64 MB hint — ignored under shared cache but enables the
        // hash-index / whole-key-filter prefetch path that turns
        // axiom-name lookups into <1 µs hits when the page is hot.
        cf_opts.optimize_for_point_lookup(64);
    } else if point_lookup_cfs.contains(&name) {
        block_opts.set_bloom_filter(10.0, false);
        cf_opts.set_block_based_table_factory(&block_opts);
    } else {
        // Range-scan / general CFs: just attach the shared cache.
        cf_opts.set_block_based_table_factory(&block_opts);
    }
    ColumnFamilyDescriptor::new(name, cf_opts)
}

/// Convert a Domain enum to a string key for indexing.
pub(crate) fn domain_to_key(domain: &Domain) -> String {
    match domain {
        Domain::PureMath => "pure_math".to_string(),
        Domain::ClassicalMechanics => "classical_mechanics".to_string(),
        Domain::Electromagnetism => "electromagnetism".to_string(),
        Domain::SpecialRelativity => "special_relativity".to_string(),
        Domain::GeneralRelativity => "general_relativity".to_string(),
        Domain::QuantumMechanics => "quantum_mechanics".to_string(),
        Domain::QuantumFieldTheory => "quantum_field_theory".to_string(),
        Domain::StatisticalMechanics => "statistical_mechanics".to_string(),
        Domain::Thermodynamics => "thermodynamics".to_string(),
        Domain::Optics => "optics".to_string(),
        Domain::FluidDynamics => "fluid_dynamics".to_string(),
        Domain::CrossDomain(domains) => {
            let keys: Vec<String> = domains.iter().map(domain_to_key).collect();
            format!("cross:{}", keys.join("+"))
        }
    }
}
