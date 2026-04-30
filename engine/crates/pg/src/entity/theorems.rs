use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

/// Verified theorems mirrored from RocksDB into PostgreSQL for relational
/// querying, leaderboards, and contributor accounting.
///
/// The 8-byte primary key and canonical hash mirror the RocksDB theorem store.
/// Array columns (`axioms_used`, `parents`, `dimension`) use PostgreSQL native
/// array types; chain and origin payloads are stored as JSONB.
#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "theorems")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false, column_type = "Binary(8)")]
    pub id: Vec<u8>,
    #[sea_orm(unique, column_type = "Binary(8)")]
    pub canonical_hash: Vec<u8>,
    /// AC-canonical hash: collapses commutativity / associativity / Eq
    /// symmetry so two formulas that differ only in operand order resolve to
    /// the same identity. Powers the `/api/search` exact-match tier. Nullable
    /// during backfill; populated by ingest going forward.
    #[sea_orm(column_type = "Binary(8)", nullable)]
    pub canonical_ac_hash: Option<Vec<u8>>,
    pub canonical_statement: String,
    pub latex: Option<String>,
    pub lean_source: String,
    pub domain: String,
    #[sea_orm(column_type = r#"custom("text[]")"#)]
    pub axioms_used: Vec<String>,
    #[sea_orm(column_type = "JsonBinary")]
    pub chain_json: Json,
    #[sea_orm(column_type = r#"custom("bytea[]")"#, nullable)]
    pub parents: Option<Vec<Vec<u8>>>,
    pub origin_kind: String,
    #[sea_orm(column_type = "JsonBinary", nullable)]
    pub origin_payload: Option<Json>,
    pub depth: Option<i32>,
    pub complexity: Option<i32>,
    pub generation: Option<i64>,
    pub fitness_novelty: Option<f32>,
    pub fitness_compactness: Option<f32>,
    pub fitness_dimensional_correctness: Option<f32>,
    pub fitness_domain_coverage: Option<f32>,
    pub fitness_axiom_efficiency: Option<f32>,
    pub fitness_nasrudin_relevance: Option<f32>,
    pub fitness_depth_score: Option<f32>,
    #[sea_orm(column_type = r#"custom("integer[]")"#, nullable)]
    pub dimension: Option<Vec<i32>>,
    pub engine_git_sha: String,
    pub lean_version: String,
    pub verification_tactic: Option<String>,
    pub verification_duration_ms: Option<i32>,
    pub verification_path: Option<String>,
    pub status: String,
    pub rejected_reason: Option<String>,
    pub contributor_id: String,
    pub created_at: DateTimeWithTimeZone,
    pub verified_at: Option<DateTimeWithTimeZone>,
    /// P-Task 12: worker locally lake-built before submitting. When
    /// true, the reverify drain treats chain-replay success as
    /// sufficient to flip directly to LakeVerified — no separate
    /// lake-promotion step.
    #[sea_orm(default_value = false)]
    pub worker_verified: bool,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
