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
pub mod cache_config;
pub mod chain;
pub mod context;
pub mod derivation;
pub mod dimension_checker;
pub mod error;
pub mod headline_registry;
pub mod lean_emitter;
pub mod lean_verify;
pub mod no_cheat_audit;
pub mod physlean_import;
pub mod postulates_classical;
pub mod postulates_gr;
pub mod postulates_quantum;
pub mod postulates_statmech;
pub mod postulates_thermo;
pub mod rewrite;
pub mod rules;
pub mod strategies;

pub use axiom_store::AxiomStore;
// Back-compat re-export: `Axiom` lives in `nasrudin-core` now (so
// the rocks crate can encode/decode it without a derive→rocks→derive
// dependency cycle). Existing callers `use nasrudin_derive::Axiom`
// keep working unchanged.
pub use nasrudin_core::Axiom;
pub use cache_config::{CacheConfig, CacheStats};
pub use chain::{Chain, RuleStep};
pub use context::{DerivationContext, DerivationStep};
pub use derivation::{DerivationEngine, DerivationResult};
pub use dimension_checker::{check_equation_dimensions, domain_variable_dimensions, equation_definitely_inconsistent, infer_dimension, sr_variable_dimensions};
pub use error::DeriveError;
pub use lean_emitter::{emit_lean_file, expr_to_lean, LeanEmitConfig};
pub use lean_verify::{LeanVerifier, LeanVerifyResult};
pub use rules::DerivationRule;
pub use strategies::DerivationStrategy;
