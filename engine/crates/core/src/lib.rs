pub mod axiom_set;
pub mod canonical_ac;
pub mod dimension;
pub mod expr;
pub mod id;
pub mod parse;
pub mod skeleton;
pub mod theorem;

pub use axiom_set::{axiom_id_from_name, axiom_set_hash, collect_axiom_ids};
pub use canonical_ac::{canonical_ac_hash, canonical_ac_string, to_canonical_ac};
pub use dimension::Dimension;
pub use expr::{BinOp, Expr, PhysConst, Symbol, UnOp};
pub use id::compute_theorem_id;
pub use skeleton::{normalise_to_skeleton, skeleton_hash, SkeletonHash};
pub use theorem::{
    AlgebraicOp, Domain, FitnessScore, ProofTree, Theorem, TheoremId, TheoremOrigin,
    VerificationStatus,
};

/// Compute a stable 8-byte canonical hash for a theorem statement.
///
/// Delegates to [`compute_theorem_id`] (xxHash64, seed 0, little-endian) and
/// returns the bytes as a `Vec<u8>` for ergonomic use with the PostgreSQL
/// mirror's `binary_len(8)` columns. This is the single source of truth for
/// the canonical theorem-identity hash across the engine.
pub fn canonical_hash(s: &str) -> Vec<u8> {
    crate::id::compute_theorem_id(s).to_vec()
}

/// Derive an 8-byte theorem ID from a canonical statement string.
///
/// In Phase 9 the theorem ID is just the canonical hash, so this is a thin
/// alias over [`canonical_hash`] kept for call-site clarity at insertion
/// points where the caller wants to express "give me the ID" intent.
pub fn theorem_id_from_canonical(s: &str) -> Vec<u8> {
    canonical_hash(s)
}
