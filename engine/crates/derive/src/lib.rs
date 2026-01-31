//! Physics derivation engine.
//!
//! Derives physics theorems (e.g., E = mc²) from axioms using algebraic
//! rewriting, then generates Lean4 proofs for formal verification.
//!
//! # Architecture
//!
//! ```text
//! AxiomStore (definitions)
//!     ↓
//! DerivationStrategy (orchestrates rules)
//!     ↓
//! DerivationRule (individual steps: substitute, simplify, sqrt)
//!     ↓
//! DerivationContext (tracks steps + produces ProofTree)
//!     ↓
//! LeanEmitter (generates .lean file)
//!     ↓
//! LeanVerifier (runs `lake build`)
//! ```

pub mod axiom_store;
pub mod context;
pub mod derivation;
pub mod dimension_checker;
pub mod error;
pub mod lean_emitter;
pub mod lean_verify;
pub mod rewrite;
pub mod rules;
pub mod strategies;

pub use axiom_store::{Axiom, AxiomStore};
pub use context::{DerivationContext, DerivationStep};
pub use derivation::{DerivationEngine, DerivationResult};
pub use dimension_checker::{check_equation_dimensions, domain_variable_dimensions, infer_dimension, sr_variable_dimensions};
pub use error::DeriveError;
pub use lean_emitter::{emit_lean_file, expr_to_lean, LeanEmitConfig};
pub use lean_verify::{LeanVerifier, LeanVerifyResult};
pub use rules::DerivationRule;
pub use strategies::DerivationStrategy;
