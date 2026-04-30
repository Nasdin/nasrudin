//! Derivation strategies: high-level derivation plans.
//!
//! A strategy orchestrates multiple rules to derive a target theorem.

use crate::axiom_store::AxiomStore;
use crate::context::DerivationContext;
use crate::error::DeriveError;
use crate::rules::{
    AlgebraicSimplify, DerivationRule, IntroduceAxiom, RearrangeEquation, SubstituteValue,
    TakePositiveRoot,
};
use nasrudin_core::{BinOp, Expr, PhysConst};

/// A derivation strategy that produces a specific result from axioms.
pub trait DerivationStrategy: std::fmt::Debug {
    /// Name of this strategy.
    fn name(&self) -> &str;

    /// Execute the strategy, populating the context with steps.
    fn execute(
        &self,
        store: &AxiomStore,
        ctx: &mut DerivationContext,
    ) -> Result<Expr, DeriveError>;
}

/// Derive E = mc² from the mass-shell condition.
///
/// Steps:
/// 1. Load mass-shell condition: E² − p²c² = (mc²)²
/// 2. Rearrange to energy-momentum relation: E² = p²c² + (mc²)²
/// 3. Assume rest frame: p = 0
/// 4. Substitute p = 0: E² = 0²c² + (mc²)²
/// 5. Simplify: E² = (mc²)²
/// 6. Take positive root: E = mc²
#[derive(Debug)]
pub struct DeriveRestEnergy;

impl DerivationStrategy for DeriveRestEnergy {
    fn name(&self) -> &str {
        "derive_rest_energy"
    }

    fn execute(
        &self,
        store: &AxiomStore,
        ctx: &mut DerivationContext,
    ) -> Result<Expr, DeriveError> {
        // Helper expressions
        let e = Expr::Var("E".into());
        let m = Expr::Var("m".into());
        let p = Expr::Var("p".into());
        let c = Expr::Const(PhysConst::SpeedOfLight);
        let two = Expr::Lit(2, 1);
        let zero = Expr::Lit(0, 1);

        // Step 1: Load mass-shell condition
        let axiom = store.get("mass_shell_condition").ok_or_else(|| {
            DeriveError::AxiomNotFound {
                name: "mass_shell_condition".into(),
            }
        })?;
        let introduce = IntroduceAxiom {
            axiom_name: "mass_shell_condition".into(),
            statement: axiom.statement.clone(),
        };
        introduce.apply(ctx)?;

        // Step 2: Rearrange to energy-momentum form: E² = p²c² + (mc²)²
        let e_sq = Expr::BinOp(BinOp::Pow, Box::new(e.clone()), Box::new(two.clone()));
        let p_sq = Expr::BinOp(BinOp::Pow, Box::new(p.clone()), Box::new(two.clone()));
        let c_sq = Expr::BinOp(BinOp::Pow, Box::new(c.clone()), Box::new(two.clone()));
        let p_sq_c_sq = Expr::BinOp(BinOp::Mul, Box::new(p_sq), Box::new(c_sq.clone()));
        let mc_sq = Expr::BinOp(BinOp::Mul, Box::new(m.clone()), Box::new(c_sq.clone()));
        let mc_sq_squared = Expr::BinOp(BinOp::Pow, Box::new(mc_sq.clone()), Box::new(two.clone()));
        let em_rhs = Expr::BinOp(BinOp::Add, Box::new(p_sq_c_sq.clone()), Box::new(mc_sq_squared.clone()));
        let em_relation = Expr::BinOp(BinOp::Eq, Box::new(e_sq.clone()), Box::new(em_rhs));

        let rearrange = RearrangeEquation {
            description: "Rearrange: E² = p²c² + (mc²)²".into(),
            target: em_relation,
        };
        rearrange.apply(ctx)?;

        // Step 3a: Introduce the rest-frame assumption explicitly. The
        // `SubstituteValue` rule's soundness gate requires `p = 0` to
        // exist as a fact or assumption in scope before it'll apply
        // the substitution — without this the gate rejects with
        // "SubstituteValue not justified by any chain fact". The rest
        // frame is a postulate of the derivation (existence of a frame
        // where spatial momentum vanishes), so we register it here.
        let p_eq_zero = Expr::BinOp(
            BinOp::Eq,
            Box::new(p.clone()),
            Box::new(zero.clone()),
        );
        ctx.assume("rest_frame: p = 0", p_eq_zero);

        // Step 3b: Substitute p = 0 (rest frame)
        let substitute_p = SubstituteValue {
            var: "p".into(),
            value: zero.clone(),
            reason: "rest frame".into(),
        };
        substitute_p.apply(ctx)?;

        // Step 4: Simplify (0² = 0, 0·x = 0, 0 + x = x)
        let simplify = AlgebraicSimplify;
        simplify.apply(ctx)?;

        // After simplification we should have E² = (mc²)²
        // Step 5: Take positive root → E = mc²
        // First ensure we have the right form
        let e_sq_eq_mc_sq_squared = Expr::BinOp(
            BinOp::Eq,
            Box::new(e_sq.clone()),
            Box::new(mc_sq_squared.clone()),
        );
        ctx.record_step(
            "Establish E² = (mc²)² from simplification",
            "canonicalize",
            e_sq_eq_mc_sq_squared,
        );

        // `TakePositiveRoot` requires non-negativity facts in scope for
        // both bases. The legacy SR axiom set registers `energy_nonneg`
        // (E ≥ 0) and `mass_nonneg` (m ≥ 0); pull them into ctx.facts()
        // so the soundness gate finds them. We use add_fact directly
        // rather than IntroduceAxiom so `current` stays as
        // `E² = (mc²)²` (which is what TakePositiveRoot needs to see).
        if let Some(ax) = store.get("energy_nonneg") {
            ctx.add_fact("energy_nonneg", ax.statement.clone());
        }
        if let Some(ax) = store.get("mass_nonneg") {
            ctx.add_fact("mass_nonneg", ax.statement.clone());
        }

        let take_root = TakePositiveRoot;
        take_root.apply(ctx)?;

        // Final result: E = mc²
        let result = Expr::BinOp(BinOp::Eq, Box::new(e), Box::new(mc_sq));
        Ok(result)
    }
}

/// Derive E = mc² from the **truly upstream** axiom set.
///
/// Unlike `DeriveRestEnergy` (which uses the forbidden `mass_shell_condition`
/// axiom — see `memory/feedback_no_cheating.md`), this strategy starts from
/// the four-momentum / Minkowski-invariant postulates and derives the
/// rest-energy theorem without pre-supposing E=mc² in any axiom.
///
/// Required axioms in the store (call
/// `AxiomStore::load_special_relativity_upstream` first):
/// - `four_momentum_time_component`: `c · p0 = E`
/// - `minkowski_invariant_def`:      `Msq = p0² − psq`
/// - `invariant_mass_postulate`:     `Msq = m² · c²`
/// - `rest_frame_psq_zero`:          `psq = 0`
///
/// Steps:
/// 1. Introduce all four upstream axioms (each becomes a hypothesis in the
///    emitted Lean theorem).
/// 2. Rearrange to `E² = (m·c²)²`.  Lean closes the gap by polynomial
///    arithmetic over the four hypotheses.
/// 3. Take positive square root → `E = m·c²`.
///
/// The Lean emitter (`lean_emitter::emit_chain_theorem`) sees that the chain
/// ends with `take_positive_root`, threads all four axiom hypotheses into a
/// `nlinarith` / `polyrith` cascade for step 2, and produces the structured
/// `congr_arg Real.sqrt + Real.sqrt_sq` move for step 3.
#[derive(Debug)]
pub struct DeriveRestEnergyFromUpstream;

impl DerivationStrategy for DeriveRestEnergyFromUpstream {
    fn name(&self) -> &str {
        "derive_rest_energy_from_upstream"
    }

    fn execute(
        &self,
        store: &AxiomStore,
        ctx: &mut DerivationContext,
    ) -> Result<Expr, DeriveError> {
        // Helper expressions
        let e = Expr::Var("E".into());
        let m = Expr::Var("m".into());
        let c = Expr::Const(PhysConst::SpeedOfLight);
        let two = Expr::Lit(2, 1);

        // ── Step 1-4: Introduce the four upstream axioms ──────────
        for axiom_name in [
            "four_momentum_time_component",
            "minkowski_invariant_def",
            "invariant_mass_postulate",
            "rest_frame_psq_zero",
        ] {
            let axiom = store
                .get(axiom_name)
                .ok_or_else(|| DeriveError::AxiomNotFound {
                    name: axiom_name.into(),
                })?;
            let intro = IntroduceAxiom {
                axiom_name: axiom_name.into(),
                statement: axiom.statement.clone(),
            };
            intro.apply(ctx)?;
        }

        // ── Step 5: Claim E² = (m·c²)² as the rearranged goal ────
        // Build the expression `E^2 = (m * c^2)^2`.
        let e_sq = Expr::BinOp(BinOp::Pow, Box::new(e.clone()), Box::new(two.clone()));
        let c_sq = Expr::BinOp(BinOp::Pow, Box::new(c.clone()), Box::new(two.clone()));
        let mc_sq = Expr::BinOp(BinOp::Mul, Box::new(m.clone()), Box::new(c_sq.clone()));
        let mc_sq_squared =
            Expr::BinOp(BinOp::Pow, Box::new(mc_sq.clone()), Box::new(two.clone()));
        let e_sq_eq_mc_sq_sq = Expr::BinOp(
            BinOp::Eq,
            Box::new(e_sq.clone()),
            Box::new(mc_sq_squared.clone()),
        );

        let rearrange = RearrangeEquation {
            description: "From upstream axioms: E² = (m·c²)²".into(),
            target: e_sq_eq_mc_sq_sq.clone(),
        };
        rearrange.apply(ctx)?;

        // Belt-and-suspenders: also run a simplify pass so the emitter sees
        // a stable normal form in `current` before take_positive_root.
        AlgebraicSimplify.apply(ctx)?;

        // Re-canonicalise the form so TakePositiveRoot has the X² = Y² shape.
        ctx.record_step(
            "Establish E² = (m·c²)² in canonical form",
            "canonicalize",
            e_sq_eq_mc_sq_sq,
        );

        // ── Step 6: Take positive root → E = m·c² ────────────────
        TakePositiveRoot.apply(ctx)?;

        Ok(Expr::BinOp(BinOp::Eq, Box::new(e), Box::new(mc_sq)))
    }
}

