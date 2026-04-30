//! Derivation chains: a `RuleStep` enum + `Chain` strategy.
//!
//! A `Chain` is an ordered sequence of `RuleStep`s that, when executed
//! against an `AxiomStore`, produces a `DerivationContext` (and thus a
//! verifiable Lean proof via the generic emitter).
//!
//! This is the *genome* type for the chain-based GA in `nasrudin-ga`.
//! Mutations insert/delete/swap rule-steps; crossover splices two
//! chains. Pre-filter: run through `chain.execute(...)` — if any rule
//! errors (rule doesn't apply to current state, axiom missing, etc.),
//! reject the chain before it reaches the Lean verifier.

use crate::axiom_store::AxiomStore;
use crate::context::DerivationContext;
use crate::error::DeriveError;
use crate::rules::{
    AlgebraicSimplify, DerivationRule, IntroduceAxiom, RearrangeEquation, SubstituteValue,
    TakePositiveRoot,
};
use crate::strategies::DerivationStrategy;
use nasrudin_core::Expr;
use serde::{Deserialize, Serialize};

/// A single step in an evolvable derivation.
///
/// Each variant corresponds to one of the 5 `DerivationRule`s, with the
/// rule's parameters baked in. The GA mutates these (insert, delete,
/// swap, parameter perturb) to explore the rewrite graph.
///
/// Serialized as `{"kind": "<Variant>", ...fields}` so the wire shape is
/// stable across worker / API boundaries (`#[serde(tag = "kind")]`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum RuleStep {
    /// Load a named axiom from the store as the new working expression.
    IntroduceAxiom { axiom_name: String },

    /// Load a previously-verified theorem as the new working expression.
    /// Functionally identical to `IntroduceAxiom` from the chain's
    /// perspective (both look up a name in the store and install its
    /// statement as the current expression), but tagged separately so
    /// the audit / search heuristics can tell "this chain composes off
    /// a peer-verified result" from "this chain starts from postulates."
    /// The `theorem_name` is the synthetic name the worker registered
    /// after seed-syncing the peer theorem (typically `peer_<hash>`).
    IntroduceTheorem { theorem_name: String },

    /// Substitute every occurrence of `var` with `value` in `current`.
    SubstituteValue {
        var: String,
        value: Expr,
        reason: String,
    },

    /// Apply algebraic identities (`x+0=x`, `x*1=x`, `x*0=0`, `x^0=1`,
    /// `x^1=x`, double-negation) to fold trivial sub-expressions.
    AlgebraicSimplify,

    /// Claim that `current` rearranges to `target`. The proof obligation
    /// is discharged by Lean (`linarith`/`nlinarith` over all collected
    /// facts + assumptions). Used for non-trivial polynomial moves.
    RearrangeEquation { description: String, target: Expr },

    /// From `LHS² = RHS²` derive `LHS = RHS` (positive square root).
    /// The Lean side handles sign hypotheses via `Real.sqrt_sq`.
    TakePositiveRoot,
}

/// An evolvable derivation chain.
///
/// `Chain(vec![...])` runs the steps in order and produces a final
/// expression (or fails). Use `chain.execute(store, &mut ctx)?` to
/// build a `DerivationContext` from which a Lean proof can be emitted
/// via `lean_emitter::emit_lean_file`.
#[derive(Debug, Clone, Default)]
pub struct Chain(pub Vec<RuleStep>);

impl Chain {
    /// New empty chain.
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Number of steps.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// True iff the chain has zero steps.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Append a step.
    pub fn push(&mut self, step: RuleStep) {
        self.0.push(step);
    }

    /// The chain that hand-codes the upstream rest-energy derivation.
    /// Used as a sanity check / regression test for the chain pipeline.
    /// (When the GA matures, no hand-coded chains will be needed for the
    /// E=mc² discovery — this just validates the infrastructure.)
    pub fn rest_energy_from_upstream() -> Self {
        use nasrudin_core::{BinOp, PhysConst};

        let e = Expr::Var("E".into());
        let m = Expr::Var("m".into());
        let c = Expr::Const(PhysConst::SpeedOfLight);
        let two = Expr::Lit(2, 1);
        let e_sq = Expr::BinOp(BinOp::Pow, Box::new(e.clone()), Box::new(two.clone()));
        let c_sq = Expr::BinOp(BinOp::Pow, Box::new(c.clone()), Box::new(two.clone()));
        let mc_sq = Expr::BinOp(BinOp::Mul, Box::new(m), Box::new(c_sq));
        let mc_sq_squared = Expr::BinOp(BinOp::Pow, Box::new(mc_sq), Box::new(two));
        let target = Expr::BinOp(BinOp::Eq, Box::new(e_sq), Box::new(mc_sq_squared));

        Chain(vec![
            RuleStep::IntroduceAxiom {
                axiom_name: "four_momentum_time_component".into(),
            },
            RuleStep::IntroduceAxiom {
                axiom_name: "minkowski_invariant_def".into(),
            },
            RuleStep::IntroduceAxiom {
                axiom_name: "invariant_mass_postulate".into(),
            },
            RuleStep::IntroduceAxiom {
                axiom_name: "rest_frame_psq_zero".into(),
            },
            // Sign axioms — discharge the non-negativity hypothesis
            // `TakePositiveRoot` requires for `E ≥ 0`. The right-hand
            // base `m·c²` is recognised structurally (m_nonneg axiom
            // below + Pow(c, 2) is even-power → ≥ 0 unconditionally).
            RuleStep::IntroduceAxiom {
                axiom_name: "energy_nonneg".into(),
            },
            RuleStep::IntroduceAxiom {
                axiom_name: "mass_nonneg".into(),
            },
            RuleStep::RearrangeEquation {
                description: "E² = (m·c²)² from upstream axioms".into(),
                target,
            },
            RuleStep::TakePositiveRoot,
        ])
    }

    /// Execute one rule step against the running context.
    fn apply_step(
        step: &RuleStep,
        store: &AxiomStore,
        ctx: &mut DerivationContext,
    ) -> Result<(), DeriveError> {
        match step {
            RuleStep::IntroduceAxiom { axiom_name } => {
                let ax = store.get(axiom_name).ok_or_else(|| {
                    DeriveError::AxiomNotFound {
                        name: axiom_name.clone(),
                    }
                })?;
                IntroduceAxiom {
                    axiom_name: axiom_name.clone(),
                    statement: ax.statement.clone(),
                }
                .apply(ctx)
            }
            // IntroduceTheorem replays identically: peer-verified
            // theorems live in the AxiomStore as synthetic axioms
            // (the worker's seed-sync registers them), so the
            // derivation rule is the same. The variant is kept
            // separate so audit and search heuristics can distinguish
            // composing-off-peer from starting-from-postulates.
            RuleStep::IntroduceTheorem { theorem_name } => {
                let ax = store.get(theorem_name).ok_or_else(|| {
                    DeriveError::AxiomNotFound {
                        name: theorem_name.clone(),
                    }
                })?;
                IntroduceAxiom {
                    axiom_name: theorem_name.clone(),
                    statement: ax.statement.clone(),
                }
                .apply(ctx)
            }
            RuleStep::SubstituteValue { var, value, reason } => SubstituteValue {
                var: var.clone(),
                value: value.clone(),
                reason: reason.clone(),
            }
            .apply(ctx),
            RuleStep::AlgebraicSimplify => AlgebraicSimplify.apply(ctx),
            RuleStep::RearrangeEquation { description, target } => RearrangeEquation {
                description: description.clone(),
                target: target.clone(),
            }
            .apply(ctx),
            RuleStep::TakePositiveRoot => TakePositiveRoot.apply(ctx),
        }
    }
}

impl DerivationStrategy for Chain {
    fn name(&self) -> &str {
        "chain"
    }

    fn execute(
        &self,
        store: &AxiomStore,
        ctx: &mut DerivationContext,
    ) -> Result<Expr, DeriveError> {
        if self.0.is_empty() {
            return Err(DeriveError::RewriteFailed {
                reason: "empty chain has no steps".into(),
            });
        }
        for step in &self.0 {
            Self::apply_step(step, store, ctx)?;
        }
        ctx.current().cloned().ok_or_else(|| DeriveError::RewriteFailed {
            reason: "chain produced no current expression".into(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derivation::DerivationEngine;
    use nasrudin_core::{BinOp, PhysConst};

    #[test]
    fn empty_chain_errors() {
        let store = AxiomStore::new();
        let chain = Chain::new();
        let mut ctx = DerivationContext::new();
        assert!(chain.execute(&store, &mut ctx).is_err());
    }

    #[test]
    fn single_introduce_chain_runs() {
        let mut engine = DerivationEngine::new();
        engine.store_mut().load_special_relativity_upstream();
        let chain = Chain(vec![RuleStep::IntroduceAxiom {
            axiom_name: "rest_frame_psq_zero".into(),
        }]);
        let mut ctx = DerivationContext::new();
        let res = chain.execute(engine.store(), &mut ctx);
        assert!(res.is_ok(), "execute returned {res:?}");
        // psq = 0
        let expected = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("psq".into())),
            Box::new(Expr::Lit(0, 1)),
        );
        assert_eq!(res.unwrap(), expected);
    }

    #[test]
    fn missing_axiom_chain_errors() {
        let store = AxiomStore::new();
        let chain = Chain(vec![RuleStep::IntroduceAxiom {
            axiom_name: "no_such_axiom".into(),
        }]);
        let mut ctx = DerivationContext::new();
        let res = chain.execute(&store, &mut ctx);
        assert!(matches!(res, Err(DeriveError::AxiomNotFound { .. })));
    }

    #[test]
    fn upstream_rest_energy_chain_executes() {
        // The hand-coded upstream chain runs without error.
        let mut engine = DerivationEngine::new();
        engine.store_mut().load_special_relativity_upstream();
        let chain = Chain::rest_energy_from_upstream();
        let mut ctx = DerivationContext::new();
        let res = chain.execute(engine.store(), &mut ctx).unwrap();
        // The final result should be E = m * c^2.
        let e = Expr::Var("E".into());
        let m = Expr::Var("m".into());
        let c = Expr::Const(PhysConst::SpeedOfLight);
        let two = Expr::Lit(2, 1);
        let c_sq = Expr::BinOp(BinOp::Pow, Box::new(c), Box::new(two));
        let mc_sq = Expr::BinOp(BinOp::Mul, Box::new(m), Box::new(c_sq));
        let expected = Expr::BinOp(BinOp::Eq, Box::new(e), Box::new(mc_sq));
        assert_eq!(res, expected);
    }
}
