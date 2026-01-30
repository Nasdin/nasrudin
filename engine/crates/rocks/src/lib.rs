//! RocksDB storage backend for the Physics Generator theorem database.
//!
//! Provides persistent storage for theorems, proofs, and lineage data using
//! column families for efficient indexed access by domain, depth, generation, etc.

use anyhow::{Context, Result};
use nasrudin_core::{Domain, ProofTree, Theorem, TheoremId, VerificationStatus};
use rocksdb::{ColumnFamilyDescriptor, IteratorMode, Options, WriteBatch, DB};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

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
];

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
    db: DB,
}

impl TheoremDb {
    /// Open or create a theorem database at the given path.
    pub fn new(path: &str) -> Result<Self> {
        let mut db_opts = Options::default();
        db_opts.create_if_missing(true);
        db_opts.create_missing_column_families(true);

        let cf_descriptors: Vec<ColumnFamilyDescriptor> = ALL_CFS
            .iter()
            .map(|name| {
                let cf_opts = Options::default();
                ColumnFamilyDescriptor::new(*name, cf_opts)
            })
            .collect();

        let db = DB::open_cf_descriptors(&db_opts, path, cf_descriptors)
            .context("Failed to open RocksDB")?;

        Ok(Self { db })
    }

    // ── Theorem CRUD ──────────────────────────────────────────────────

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

        // Lineage record
        let cf_lineage = self
            .db
            .cf_handle(CF_LINEAGE)
            .context("Missing lineage CF")?;
        let lineage = LineageRecord {
            theorem_id: theorem.id,
            parents: theorem.parents.clone(),
            children: theorem.children.clone(),
            axiom_ancestors: vec![],
        };
        let lineage_value =
            serde_json::to_vec(&lineage).context("Failed to serialize lineage")?;
        batch.put_cf(&cf_lineage, theorem.id, &lineage_value);

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

    /// List theorem IDs for a given domain.
    pub fn list_by_domain(&self, domain: &Domain) -> Result<Vec<TheoremId>> {
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
            // Stop if we've passed the prefix
            if !key.starts_with(prefix.as_bytes()) {
                break;
            }
            let mut id = [0u8; 8];
            id.copy_from_slice(&value[..8]);
            ids.push(id);
        }
        Ok(ids)
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
                let stats: DbStats =
                    serde_json::from_slice(&bytes).context("Failed to deserialize stats")?;
                Ok(stats)
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

    /// List theorem IDs at a given derivation depth.
    pub fn list_by_depth(&self, depth: u32) -> Result<Vec<TheoremId>> {
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
        }
        Ok(ids)
    }

    /// List theorem IDs from a given generation.
    pub fn list_by_generation(&self, generation: u64) -> Result<Vec<TheoremId>> {
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
        }
        Ok(ids)
    }

    /// List theorem IDs derived from a given parent/axiom.
    pub fn list_by_axiom(&self, axiom_id: &TheoremId) -> Result<Vec<TheoremId>> {
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
        }
        Ok(ids)
    }

    /// Prefix search on the LaTeX index. Returns theorem IDs whose normalized
    /// LaTeX starts with the given prefix.
    pub fn search_latex(&self, prefix: &str) -> Result<Vec<TheoremId>> {
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
        }
        Ok(ids)
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
            if let Some(thm) = self.get_theorem(id)? {
                theorems.push(thm);
            }
        }
        Ok(theorems)
    }

    /// Count theorems per domain by scanning the by_domain CF.
    pub fn count_by_domain(&self) -> Result<HashMap<String, u64>> {
        let cf = self
            .db
            .cf_handle(CF_BY_DOMAIN)
            .context("Missing by_domain CF")?;
        let mut counts: HashMap<String, u64> = HashMap::new();
        let iter = self.db.iterator_cf(&cf, IteratorMode::Start);
        for item in iter {
            let (key, _) = item.context("Failed to iterate by_domain")?;
            let key_str = String::from_utf8_lossy(&key);
            if let Some(domain) = key_str.split(':').next() {
                *counts.entry(domain.to_string()).or_insert(0) += 1;
            }
        }
        Ok(counts)
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

/// Convert a Domain enum to a string key for indexing.
fn domain_to_key(domain: &Domain) -> String {
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
