//! Boot-time RocksDB hydration from PostgreSQL.
//!
//! Phase 9 disaster-recovery path: when a fresh node mounts a Postgres backup
//! but starts with an empty RocksDB (e.g. a freshly-provisioned droplet, a
//! lost volume, or a manual reseed), [`hydrate_rocks_from_pg_if_empty`]
//! repopulates the embedded store from the relational mirror so the GA, API,
//! and verifiers see the existing corpus on first boot.
//!
//! Design rules (from the Phase 9 spec):
//!
//! - **Skip when RocksDB is non-empty.** We use `get_stats().total_theorems`
//!   as the cheap "has anything" probe so a normal restart pays no scan cost.
//! - **Paginate by 8-byte BYTEA primary key, ASC.** RocksDB is sized in the
//!   millions; loading everything into memory at once is not an option. The
//!   `id` column is a btree-indexable BYTEA so `id > $cursor` is the right
//!   cursor shape.
//! - **Per-row failures don't abort the batch.** Hydration is a recovery
//!   path; one corrupt row should never stop the rest of the corpus from
//!   coming back online. Failures log + skip.
//! - **Restartable on full success or fresh wipe of RocksDB.** A crash
//!   partway through hydration leaves `stats.total_theorems > 0`, which
//!   causes the next boot to skip hydration — operator must wipe
//!   `/data/rocks/` and retry to recover the missed rows. There is no
//!   resumable cursor today; the skip-when-empty gate trades partial-crash
//!   recovery for a cheap normal-restart path.
//!
//! ## Conversion concerns
//!
//! The Postgres `theorems` row carries far more fields than the Phase 9
//! `core::Theorem` round-trip needs. We populate only what
//! `TheoremDb::put_theorem` actually reads from the struct (id, statement,
//! domain, depth, generation, parents, verified status, origin) plus enough
//! filler that serde serialization succeeds. Fitness components, dimension,
//! and the full proof tree are dropped — they are reconstructible from the
//! `chain_json` payload in later phases or simply not load-bearing for the
//! embedded indexes today.
//!
//! The `Theorem.statement` field of a hydrated row is a placeholder
//! `Expr::Var(canonical_statement)` — the original AST structure is not
//! reconstructed. RocksDB indexes don't read `statement`, so this is safe
//! for browsing / leaderboards, but downstream rewrite / mutation passes
//! must skip hydrated theorems or re-parse the canonical_statement.

use std::sync::Arc;

use anyhow::{Result, anyhow};
use sea_orm::{ColumnTrait, DatabaseConnection, EntityTrait, QueryFilter, QueryOrder, QuerySelect};

use nasrudin_core::{
    Domain, Expr, FitnessScore, ProofTree, Theorem, TheoremId, TheoremOrigin, VerificationStatus,
};
use nasrudin_pg::entity::theorems as ent;
use nasrudin_rocks::TheoremDb;

/// Hydrate RocksDB from the Postgres `theorems` mirror if (and only if) the
/// embedded store is empty.
///
/// Walks `theorems WHERE status = 'Verified'` ordered by `id ASC` in 1000-row
/// batches and calls [`TheoremDb::put_theorem`] for each. Returns `Ok(())`
/// after either the skip or a successful pass; per-row conversion / write
/// failures are logged and skipped so one bad row cannot abort recovery.
pub async fn hydrate_rocks_from_pg_if_empty(
    rocks: &Arc<TheoremDb>,
    pg: &DatabaseConnection,
) -> Result<()> {
    let stats = rocks.get_stats()?;
    if stats.total_theorems > 0 {
        tracing::info!(
            theorems = stats.total_theorems,
            "RocksDB non-empty, skipping hydration"
        );
        return Ok(());
    }

    tracing::info!("RocksDB empty, hydrating from Postgres");

    let mut count: u64 = 0;
    let mut last_id: Option<Vec<u8>> = None;

    loop {
        let mut q = ent::Entity::find()
            .filter(ent::Column::Status.eq("Verified"))
            .order_by_asc(ent::Column::Id)
            .limit(1000);
        if let Some(id) = last_id.as_ref() {
            q = q.filter(ent::Column::Id.gt(id.clone()));
        }

        let batch = q.all(pg).await?;
        if batch.is_empty() {
            break;
        }
        last_id = batch.last().map(|m| m.id.clone());

        for row in batch {
            let id_hex = hex::encode(&row.id);
            match pg_row_to_core_theorem(&row) {
                Ok(theorem) => match rocks.put_theorem(&theorem) {
                    Ok(()) => count += 1,
                    Err(e) => tracing::warn!(
                        theorem_id = %id_hex,
                        err = %e,
                        "hydration: put_theorem failed, skipping"
                    ),
                },
                Err(e) => tracing::warn!(
                    theorem_id = %id_hex,
                    err = %e,
                    "hydration: convert failed, skipping"
                ),
            }
        }
    }

    tracing::info!(count, "hydration complete");
    Ok(())
}

/// Convert a Postgres `theorems` row into a `core::Theorem` suitable for
/// `TheoremDb::put_theorem`.
///
/// This is intentionally a minimal mapping: it preserves enough identity
/// (`id`, `statement`, `domain`, `parents`, `depth`, `generation`) for the
/// RocksDB secondary indexes and stats counters to work, and stamps the
/// theorem as `Verified` so it shows up in verified-only queries. Lossy on
/// fitness, dimension, and the full proof tree — see the module docs for the
/// rationale.
fn pg_row_to_core_theorem(row: &ent::Model) -> Result<Theorem> {
    if row.id.len() != 8 {
        return Err(anyhow!(
            "theorem id length != 8: got {} bytes",
            row.id.len()
        ));
    }
    let mut id: TheoremId = [0u8; 8];
    id.copy_from_slice(&row.id);

    let parents: Vec<TheoremId> = row
        .parents
        .as_ref()
        .map(|ps| {
            ps.iter()
                .filter_map(|p| {
                    if p.len() == 8 {
                        let mut a = [0u8; 8];
                        a.copy_from_slice(p);
                        Some(a)
                    } else {
                        tracing::warn!(
                            parent_len = p.len(),
                            "hydration: skipping malformed parent id"
                        );
                        None
                    }
                })
                .collect()
        })
        .unwrap_or_default();

    let domain = parse_domain(&row.domain);

    // The proof tree field is required by serde but the embedded indexes
    // never traverse it in Phase 9 — a TacticProof leaf carrying the Lean
    // source as its tactic string is the cheapest legal value.
    let proof = ProofTree::TacticProof {
        tactic: row.lean_source.clone(),
        proof_term: Vec::new(),
    };

    let verified = VerificationStatus::Verified {
        proof_term: Vec::new(),
        tactic_used: row.verification_tactic.clone().unwrap_or_default(),
    };

    Ok(Theorem {
        id,
        statement: Expr::Var(row.canonical_statement.clone()),
        canonical: row.canonical_statement.clone(),
        latex: row.latex.clone().unwrap_or_default(),
        proof,
        depth: row.depth.unwrap_or(0).max(0) as u32,
        complexity: row.complexity.unwrap_or(0).max(0) as u32,
        domain,
        dimension: None,
        parents,
        children: Vec::new(),
        verified,
        fitness: FitnessScore::default(),
        generation: row.generation.unwrap_or(0).max(0) as u64,
        created_at: row
            .verified_at
            .unwrap_or(row.created_at)
            .timestamp_micros()
            .max(0) as u64,
        // Phase 9: simplified — future phases parse `origin_kind` /
        // `origin_payload` to reconstitute Crossover / Mutation / DomainTransfer.
        // Tag as `Imported` rather than `Axiom` so `TheoremDb::increment_stats`
        // doesn't bump `total_axioms` for every hydrated row.
        origin: TheoremOrigin::Imported {
            source: "hydration_from_pg".to_string(),
        },
    })
}

/// Map the Postgres `domain` text column back to the `core::Domain` enum.
///
/// Accepts both the Rust enum names (e.g. `"SpecialRelativity"`, used by the
/// API ingest path) and the snake_case `Display` form (e.g.
/// `"special_relativity"`, used by some legacy importers). Unknown values
/// fall through to `PureMath` so a one-off taxonomy drift doesn't drop the
/// row entirely.
fn parse_domain(s: &str) -> Domain {
    match s {
        "SpecialRelativity" | "special_relativity" => Domain::SpecialRelativity,
        "Electromagnetism" | "electromagnetism" => Domain::Electromagnetism,
        "ClassicalMechanics" | "classical_mechanics" => Domain::ClassicalMechanics,
        "QuantumMechanics" | "quantum_mechanics" => Domain::QuantumMechanics,
        "Thermodynamics" | "thermodynamics" => Domain::Thermodynamics,
        "GeneralRelativity" | "general_relativity" => Domain::GeneralRelativity,
        "QuantumFieldTheory" | "quantum_field_theory" => Domain::QuantumFieldTheory,
        "StatisticalMechanics" | "statistical_mechanics" => Domain::StatisticalMechanics,
        "Optics" | "optics" => Domain::Optics,
        "FluidDynamics" | "fluid_dynamics" => Domain::FluidDynamics,
        "PureMath" | "pure_math" => Domain::PureMath,
        other => {
            tracing::warn!(domain = %other, "hydration: unknown domain, defaulting to PureMath");
            Domain::PureMath
        }
    }
}
