//! Top-level derivation engine.
//!
//! Coordinates axiom loading, strategy execution, Lean emission, and verification.

use crate::axiom_store::AxiomStore;
use crate::context::DerivationContext;
use crate::dimension_checker;
use crate::error::DeriveError;
use crate::lean_emitter::{self, LeanEmitConfig};
use crate::lean_verify::{LeanVerifier, LeanVerifyResult};
use crate::strategies::{DerivationStrategy, DeriveRestEnergy};
use nasrudin_core::{Dimension, Expr};

/// Result of a successful derivation.
#[derive(Debug, Clone)]
pub struct DerivationResult {
    /// The derived theorem as an expression.
    pub theorem: Expr,
    /// Human-readable derivation steps.
    pub steps: Vec<String>,
    /// Generated Lean4 proof file content.
    pub lean_source: String,
    /// Dimension of the equation (if checkable).
    pub dimension: Option<Dimension>,
}

/// The top-level derivation engine.
#[derive(Debug)]
pub struct DerivationEngine {
    store: AxiomStore,
}

impl DerivationEngine {
    /// Create a new derivation engine with no axioms loaded.
    pub fn new() -> Self {
        Self {
            store: AxiomStore::new(),
        }
    }

    /// Create an engine pre-loaded with axioms from the PhysLean catalog.
    ///
    /// Falls back to the legacy SR axioms if the catalog is not found.
    pub fn with_catalog_axioms() -> Self {
        let mut engine = Self::new();
        // Try catalog first, fall back to legacy
        let catalog_path = std::path::Path::new("physlean-extract/output/catalog.json");
        match engine.store.load_from_catalog(catalog_path) {
            Ok(count) => {
                tracing::info!("Loaded {count} axioms from PhysLean catalog");
            }
            Err(e) => {
                tracing::warn!("Failed to load catalog ({e}), using legacy SR axioms");
                #[allow(deprecated)]
                engine.store.load_special_relativity();
            }
        }
        engine
    }

    /// Create an engine pre-loaded with special relativity axioms.
    #[deprecated(note = "Use with_catalog_axioms() for PhysLean-sourced axioms")]
    pub fn with_sr_axioms() -> Self {
        let mut engine = Self::new();
        #[allow(deprecated)]
        engine.store.load_special_relativity();
        engine
    }

    /// Access the axiom store.
    pub fn store(&self) -> &AxiomStore {
        &self.store
    }

    /// Access the axiom store mutably.
    pub fn store_mut(&mut self) -> &mut AxiomStore {
        &mut self.store
    }

    /// Run a derivation strategy and return the result.
    pub fn derive_by_strategy(
        &self,
        strategy: &dyn DerivationStrategy,
    ) -> Result<(Expr, DerivationContext), DeriveError> {
        let mut ctx = DerivationContext::new();
        let result = strategy.execute(&self.store, &mut ctx)?;
        Ok((result, ctx))
    }

    /// Derive E = mc² from SR axioms.
    pub fn derive_rest_energy(&self) -> Result<DerivationResult, DeriveError> {
        let strategy = DeriveRestEnergy;
        let (theorem, ctx) = self.derive_by_strategy(&strategy)?;

        // Generate Lean source
        let config = LeanEmitConfig::default();
        let lean_source = lean_emitter::emit_lean_file(&ctx, &config);

        // Check dimensions
        let var_dims = dimension_checker::sr_variable_dimensions();
        let dimension = dimension_checker::check_equation_dimensions(&theorem, &var_dims).ok();

        let steps = ctx
            .steps()
            .iter()
            .map(|s| format!("{}: {}", s.rule, s.description))
            .collect();

        Ok(DerivationResult {
            theorem,
            steps,
            lean_source,
            dimension,
        })
    }

    /// Derive and then verify via Lean4.
    pub fn derive_and_verify(
        &self,
        prover_root: impl Into<std::path::PathBuf>,
    ) -> Result<DerivationResult, DeriveError> {
        let result = self.derive_rest_energy()?;

        let verifier = LeanVerifier::new(prover_root);
        let verify_result = verifier.verify_file(
            &result.lean_source,
            "PhysicsGenerator.Derived.AutoRestEnergy",
        );

        match verify_result {
            LeanVerifyResult::Success => {
                tracing::info!("Lean4 verification succeeded");
                Ok(result)
            }
            LeanVerifyResult::Failed { stderr } => {
                Err(DeriveError::LeanVerificationFailed { reason: stderr })
            }
            LeanVerifyResult::ProcessError { message } => {
                Err(DeriveError::LeanVerificationFailed { reason: message })
            }
        }
    }
}

impl Default for DerivationEngine {
    fn default() -> Self {
        Self::new()
    }
}
