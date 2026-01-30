//! RocksDB storage backend for the Physics Generator theorem database.
//!
//! Provides persistent storage for theorems, proofs, and lineage data using
//! column families for efficient indexed access by domain, depth, generation, etc.

use anyhow::{Context, Result};
use physics_core::{Theorem, TheoremId};
use rocksdb::{ColumnFamilyDescriptor, Options, DB};
use serde::{Deserialize, Serialize};

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

    /// Store a theorem in the database.
    pub fn put_theorem(&self, theorem: &Theorem) -> Result<()> {
        let cf = self
            .db
            .cf_handle(CF_THEOREMS)
            .context("Missing theorems CF")?;
        let key = theorem.id;
        let value = serde_json::to_vec(theorem).context("Failed to serialize theorem")?;
        self.db
            .put_cf(&cf, key, value)
            .context("Failed to put theorem")?;
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
}
