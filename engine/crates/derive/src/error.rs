//! Error types for the derivation engine.

use thiserror::Error;

/// Errors that can occur during derivation.
#[derive(Debug, Error)]
pub enum DeriveError {
    /// An axiom required by the derivation was not found.
    #[error("axiom not found: {name}")]
    AxiomNotFound { name: String },

    /// A rewrite rule could not be applied.
    #[error("rewrite failed: {reason}")]
    RewriteFailed { reason: String },

    /// A substitution target was not found in the expression.
    #[error("substitution target not found: variable `{var}`")]
    SubstitutionFailed { var: String },

    /// Dimensional analysis detected an inconsistency.
    #[error("dimension mismatch: expected {expected}, got {got}")]
    DimensionMismatch { expected: String, got: String },

    /// The derivation strategy could not complete.
    #[error("strategy failed: {strategy}: {reason}")]
    StrategyFailed { strategy: String, reason: String },

    /// Lean verification rejected the proof.
    #[error("lean verification failed: {reason}")]
    LeanVerificationFailed { reason: String },

    /// IO error during Lean file operations.
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
}
