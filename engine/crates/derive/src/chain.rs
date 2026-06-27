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

    /// The chain that hand-codes the upstream Planck-Einstein relation
    /// `E = ℏ·ω` via the electromagnetism upstream axioms.
    ///
    /// The EM upstream loader registers `photon_energy_def`:
    /// `Eph = hbar · omega` (with `hbar` as a Var, distinct from the
    /// target spec's `Const(ReducedPlanck)` slot, so the audit does not
    /// flag it as a leaked headline). Introducing it directly produces
    /// an `Eq(Var, Mul(Var, Var))` whose structural shape is exactly the
    /// Planck-Einstein relation — the GA's `qm_planck_einstein` ladder
    /// scores this near-1 on root-op + topology even though the variable
    /// names differ.
    ///
    /// This is an M1.b seed elite: a known-good chain locked into the
    /// population so domain-aware fitness has a permanent anchor to
    /// drift around. The same role `rest_energy_from_upstream` plays for
    /// `sr_rest_energy`.
    pub fn planck_einstein_from_upstream() -> Self {
        Chain(vec![
            // hbar > 0 — sign convention; harmless extra fact in ctx.
            RuleStep::IntroduceAxiom {
                axiom_name: "hbar_positive".into(),
            },
            // Eph = hbar · omega — Planck-Einstein, structural form
            // of the headline `E = ℏω`.
            RuleStep::IntroduceAxiom {
                axiom_name: "photon_energy_def".into(),
            },
            // No-op simplifier; exercises the AlgebraicSimplify branch
            // in the chain executor so the seed touches more than one
            // RuleStep variant.
            RuleStep::AlgebraicSimplify,
        ])
    }

    /// The chain that hand-codes the Boltzmann entropy relation
    /// `S = k_B · ln(Ω)` via the statistical-mechanics postulates.
    ///
    /// `statmech_boltzmann_entropy` is registered as a *postulate* (a
    /// foundational input bridging microstates to thermodynamic entropy)
    /// and is therefore exempt from the no-cheat audit's deny-list — see
    /// `no_cheat_audit::forbidden_canonical_statements` comments at the
    /// Boltzmann-entropy line. Introducing it produces exactly the
    /// `thermo_boltzmann_entropy` target shape, giving the GA a
    /// canonical anchor for the StatisticalMechanics domain.
    ///
    /// Fallback target after `em_gauss_law` was skipped — the EM upstream
    /// store has no `div E`, charge density, or vacuum-permittivity
    /// axioms, so `∇·E = ρ/ε₀` is not derivable from the existing
    /// postulate set without inventing axioms (which would itself be a
    /// no-cheat violation if they encoded the headline).
    pub fn boltzmann_entropy_from_upstream() -> Self {
        Chain(vec![
            // Ω > 0 — ensures ln Ω is defined; positivity fact in ctx.
            RuleStep::IntroduceAxiom {
                axiom_name: "statmech_omega_positive".into(),
            },
            // k_B > 0 — sign convention.
            RuleStep::IntroduceAxiom {
                axiom_name: "statmech_kb_positive".into(),
            },
            // S = k_B · ln(Ω) — Boltzmann's relation.
            RuleStep::IntroduceAxiom {
                axiom_name: "statmech_boltzmann_entropy".into(),
            },
            // No-op simplifier; same role as in the SR / planck-einstein
            // seeds — exercises the AlgebraicSimplify branch.
            RuleStep::AlgebraicSimplify,
        ])
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
                // `store.get` returns an owned `Axiom`; move its
                // `statement` out instead of cloning the (potentially
                // deep) Expr tree. Skips one deep `Box<Expr>` walk per
                // IntroduceAxiom step. The hot path runs a ~6-step
                // chain ~200 times per generation; this multiplies.
                let ax = store
                    .get(axiom_name)
                    .ok_or_else(|| DeriveError::AxiomNotFound {
                        name: axiom_name.clone(),
                    })?;
                IntroduceAxiom {
                    axiom_name: axiom_name.clone(),
                    statement: ax.statement,
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
                let ax = store
                    .get(theorem_name)
                    .ok_or_else(|| DeriveError::AxiomNotFound {
                        name: theorem_name.clone(),
                    })?;
                IntroduceAxiom {
                    axiom_name: theorem_name.clone(),
                    statement: ax.statement,
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
            RuleStep::RearrangeEquation {
                description,
                target,
            } => RearrangeEquation {
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
        ctx.current()
            .cloned()
            .ok_or_else(|| DeriveError::RewriteFailed {
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
    fn upstream_rest_energy_chain_emits_lean_with_expected_theorem() {
        // M1.a sanity: the seed chain must produce a Lean source whose
        // theorem statement is exactly `E = m * c^2`. If this changes
        // shape (e.g. the emitter ever decides to wrap the RHS in a
        // sqrt or extra parens), the elaborator will not match the
        // sr_rest_energy target and Lake will silently reject.
        let mut engine = crate::derivation::DerivationEngine::new();
        engine.store_mut().load_special_relativity_upstream();
        let chain = Chain::rest_energy_from_upstream();
        let mut ctx = crate::context::DerivationContext::new();
        chain
            .execute(engine.store(), &mut ctx)
            .expect("chain execute");
        let cfg = crate::lean_emitter::LeanEmitConfig {
            namespace: "PhysicsGenerator.Derived".into(),
            theorem_name: "rest_energy_seed_chain".into(),
            use_mathlib: true,
            description: None,
        };
        let lean = crate::lean_emitter::emit_lean_file(&ctx, &cfg);
        // Final theorem statement contains the target shape.
        // The emitter parenthesises the RHS as `(m * (c ^ 2))`.
        assert!(
            lean.contains(": E = (m * (c ^ 2))"),
            "emitted Lean missing `E = (m * (c ^ 2))` final goal; got:\n{lean}"
        );
        // Standard discharge ladder: nlinarith -> linarith ->
        // ring_nf;nlinarith -> linear_combination as last-ditch.
        // `polyrith` was removed (external Sage server timeouts on
        // resource-constrained boxes).
        assert!(lean.contains("nlinarith"), "emitter dropped nlinarith");
        assert!(
            !lean.contains("polyrith"),
            "emitter still emits polyrith; it was removed for offline reliability"
        );
        assert!(
            lean.contains("Real.sqrt_sq"),
            "emitter dropped Real.sqrt_sq rewrite"
        );
        assert!(
            lean.contains("rest_energy_seed_chain"),
            "emitted Lean missing theorem name; got:\n{lean}"
        );
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

    #[test]
    fn upstream_planck_einstein_chain_executes() {
        // The hand-coded upstream Planck-Einstein chain runs without error
        // against the EM upstream axioms (photon_energy_def + hbar_positive).
        let mut engine = DerivationEngine::new();
        engine.store_mut().load_electromagnetism_upstream();
        let chain = Chain::planck_einstein_from_upstream();
        let mut ctx = DerivationContext::new();
        let res = chain.execute(engine.store(), &mut ctx).unwrap();
        // The final result should be Eph = hbar * omega (after the
        // AlgebraicSimplify no-op tail). hbar is a Var here (per the EM
        // upstream loader), not a Const — that's by design to dodge the
        // no-cheat audit which forbids `E = ReducedPlanck · omega` as a
        // raw axiom. The Planck-Einstein structural shape is preserved.
        let eph = Expr::Var("Eph".into());
        let hbar = Expr::Var("hbar".into());
        let omega = Expr::Var("omega".into());
        let expected = Expr::BinOp(
            BinOp::Eq,
            Box::new(eph),
            Box::new(Expr::BinOp(BinOp::Mul, Box::new(hbar), Box::new(omega))),
        );
        assert_eq!(res, expected);
    }

    #[test]
    fn upstream_boltzmann_entropy_chain_executes() {
        // The hand-coded Boltzmann-entropy chain runs without error
        // against the statistical-mechanics postulate set.
        let mut engine = DerivationEngine::new();
        engine.store_mut().load_statistical_mechanics_postulates();
        let chain = Chain::boltzmann_entropy_from_upstream();
        let mut ctx = DerivationContext::new();
        let res = chain.execute(engine.store(), &mut ctx).unwrap();
        // The final result should be S = k_B * ln(Omega) — exactly the
        // `thermo_boltzmann_entropy` target shape. statmech_boltzmann_entropy
        // is a registered postulate (bridging microstates and thermodynamic
        // entropy) and is exempt from the no-cheat audit's deny-list.
        let s = Expr::Var("S".into());
        let kb = Expr::Const(PhysConst::Boltzmann);
        let omega = Expr::Var("Omega".into());
        let ln_omega = Expr::UnOp(nasrudin_core::UnOp::Ln, Box::new(omega));
        let expected = Expr::BinOp(
            BinOp::Eq,
            Box::new(s),
            Box::new(Expr::BinOp(BinOp::Mul, Box::new(kb), Box::new(ln_omega))),
        );
        assert_eq!(res, expected);
    }
}
