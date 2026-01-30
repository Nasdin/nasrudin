//! Lean4 FFI bridge for formal proof verification.
//!
//! This crate provides the interface between the Rust engine and the Lean4
//! proof checker. Two verification paths are available:
//!
//! 1. **Process-based** (`process` module): Generates `.lean` files and runs
//!    `lake build`. This is the primary path and works out of the box.
//!
//! 2. **C FFI** (`ffi` module, feature-gated behind `lean-ffi`): Links against
//!    the compiled Lean4 static library for in-process verification.
//!    Requires `lake build` of the prover first.
//!
//! Supporting modules:
//! - `lean_syntax`: Converts `Expr` AST → Lean4 source code
//! - `tactic`: Tactic cascade configuration (omega → grind)
//! - `export`: Standalone `.lean` file generation for academic verification

pub mod export;
pub mod ffi;
pub mod lean_syntax;
pub mod process;
pub mod tactic;

use anyhow::Result;
use nasrudin_core::{Expr, Theorem};

pub use process::{ProcessVerifier, ProcessVerifyConfig};

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
/// Provides both process-based and (optionally) FFI-based verification.
/// Use `LeanBridge::new()` for the default process-based path, or
/// `LeanBridge::with_ffi()` when the `lean-ffi` feature is enabled.
pub struct LeanBridge {
    process_verifier: Option<ProcessVerifier>,
    #[cfg(feature = "lean-ffi")]
    ffi_initialized: bool,
}

impl LeanBridge {
    /// Create a Lean4 bridge using process-based verification.
    pub fn new() -> Result<Self> {
        let config = ProcessVerifyConfig::from_env();
        let verifier = ProcessVerifier::new(config);

        if verifier.check_available()? {
            tracing::info!("LeanBridge: process-based verification available");
        } else {
            tracing::warn!("LeanBridge: lake/prover not found — verification will fail");
        }

        Ok(Self {
            process_verifier: Some(verifier),
            #[cfg(feature = "lean-ffi")]
            ffi_initialized: false,
        })
    }

    /// Create a bridge with FFI verification (requires `lean-ffi` feature).
    #[cfg(feature = "lean-ffi")]
    pub fn with_ffi() -> Result<Self> {
        ffi::safe::init().map_err(|e| anyhow::anyhow!(e))?;
        tracing::info!("LeanBridge: FFI verification initialized");

        Ok(Self {
            process_verifier: Some(ProcessVerifier::new(ProcessVerifyConfig::from_env())),
            ffi_initialized: true,
        })
    }

    /// Verify a theorem using the best available method.
    ///
    /// Tries FFI first (if available), then falls back to process-based.
    pub fn verify_theorem(&self, theorem: &Theorem) -> Result<VerifyResult> {
        // FFI path (if compiled with lean-ffi feature)
        #[cfg(feature = "lean-ffi")]
        if self.ffi_initialized {
            let result = ffi::safe::verify(&theorem.canonical);
            return Ok(result);
        }

        // Process-based path
        if let Some(ref verifier) = self.process_verifier {
            return verifier.verify_theorem(theorem);
        }

        Ok(VerifyResult::FfiError {
            message: "No verification backend available".to_string(),
        })
    }

    /// Verify a raw expression by statement and domain.
    pub fn verify_expr(
        &self,
        statement: &Expr,
        domain: &nasrudin_core::Domain,
    ) -> Result<VerifyResult> {
        let canonical = statement.to_canonical();

        #[cfg(feature = "lean-ffi")]
        if self.ffi_initialized {
            return Ok(ffi::safe::verify(&canonical));
        }

        if let Some(ref verifier) = self.process_verifier {
            return verifier.verify_canonical(&canonical, statement, domain);
        }

        Ok(VerifyResult::FfiError {
            message: "No verification backend available".to_string(),
        })
    }

    /// Attempt to simplify an expression using Lean4 tactics.
    ///
    /// Only available with the `lean-ffi` feature. Returns `None` otherwise.
    pub fn simplify(&self, expr: &Expr) -> Option<String> {
        #[cfg(feature = "lean-ffi")]
        if self.ffi_initialized {
            let canonical = expr.to_canonical();
            return ffi::safe::simplify(&canonical).ok();
        }

        let _ = expr;
        None
    }

    /// Verify a proof via `lake build` (legacy convenience method).
    pub fn verify_via_lake(
        &self,
        prover_root: &std::path::Path,
        module_path: &str,
    ) -> Result<bool> {
        export::verify_via_lake(prover_root, module_path)
    }

    /// Check if any verification backend is available.
    pub fn is_available(&self) -> bool {
        #[cfg(feature = "lean-ffi")]
        if self.ffi_initialized {
            return true;
        }

        self.process_verifier
            .as_ref()
            .and_then(|v| v.check_available().ok())
            .unwrap_or(false)
    }
}

impl Default for LeanBridge {
    fn default() -> Self {
        Self {
            process_verifier: None,
            #[cfg(feature = "lean-ffi")]
            ffi_initialized: false,
        }
    }
}

impl Drop for LeanBridge {
    fn drop(&mut self) {
        #[cfg(feature = "lean-ffi")]
        if self.ffi_initialized {
            ffi::safe::shutdown();
        }
    }
}
