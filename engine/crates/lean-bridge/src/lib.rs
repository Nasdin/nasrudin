//! Lean4 FFI bridge for formal proof verification.
//!
//! This crate will provide the interface between the Rust engine and the Lean4
//! proof checker. Currently stubbed -- the FFI will be wired once the Lean4
//! prover component (`lean/PhysicsProver`) is built.
//!
//! The bridge will:
//! - Convert `Expr` trees to Lean4 terms
//! - Submit proof obligations to the Lean4 kernel
//! - Return verification results (verified / rejected / timeout)
//! - Optionally run Lean4 tactics for automated proof search

use anyhow::Result;
use physics_core::Expr;

/// Result of a Lean4 verification attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyResult {
    /// The proof was verified by the Lean4 kernel.
    Verified {
        /// Serialized proof term from Lean4.
        proof_term: Vec<u8>,
    },
    /// The proof was rejected.
    Rejected {
        /// Human-readable rejection reason.
        reason: String,
    },
    /// Verification timed out.
    Timeout,
    /// The expression could not be parsed into a Lean4 term.
    ParseError {
        /// Description of the parse failure.
        message: String,
    },
    /// An FFI-level error occurred.
    FfiError {
        /// Description of the FFI failure.
        message: String,
    },
}

/// Bridge to the Lean4 proof verification kernel.
///
/// This struct manages the lifecycle of the Lean4 environment and provides
/// methods for proof verification and expression simplification.
pub struct LeanBridge {
    // Will hold the Lean4 environment handle once FFI is implemented.
    _initialized: bool,
}

impl LeanBridge {
    /// Create a new Lean4 bridge.
    ///
    /// In the future this will initialize the Lean4 runtime and load the
    /// `PhysicsProver` library. Currently returns a stub instance.
    pub fn new() -> Result<Self> {
        tracing::warn!("LeanBridge: using stub implementation -- Lean4 FFI not yet wired");
        Ok(Self {
            _initialized: false,
        })
    }

    /// Verify a proof obligation.
    ///
    /// Takes a theorem statement and a proof term, and asks the Lean4 kernel
    /// to check the proof. Returns `VerifyResult::Verified` if the proof is
    /// valid.
    ///
    /// Currently always returns `FfiError` since Lean4 is not yet connected.
    pub fn verify(&self, _statement: &Expr, _proof_term: &[u8]) -> VerifyResult {
        // TODO: Wire up Lean4 FFI
        // 1. Convert Expr -> Lean4 Expr via lean_sys
        // 2. Submit to Lean4 kernel
        // 3. Parse result
        VerifyResult::FfiError {
            message: "Lean4 FFI not yet implemented".to_string(),
        }
    }

    /// Attempt to simplify an expression using Lean4 tactics.
    ///
    /// Uses Lean4's `simp` and custom physics tactics to reduce expressions.
    /// Returns `None` if no simplification was found.
    ///
    /// Currently always returns `None` since Lean4 is not yet connected.
    pub fn simplify(&self, _expr: &Expr) -> Option<Expr> {
        // TODO: Wire up Lean4 FFI for simplification
        None
    }
}

impl Default for LeanBridge {
    fn default() -> Self {
        Self {
            _initialized: false,
        }
    }
}
