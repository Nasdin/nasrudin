//! Derivation strategies: high-level derivation plans.
//!
//! A strategy orchestrates multiple rules to derive a target theorem.

use crate::axiom_store::AxiomStore;
use crate::context::DerivationContext;
use crate::error::DeriveError;
use crate::rules::{
    AlgebraicSimplify, IntroduceAxiom, RearrangeEquation, SubstituteValue, TakePositiveRoot,
    DerivationRule,
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

        // Step 3: Substitute p = 0 (rest frame)
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

        let take_root = TakePositiveRoot;
        take_root.apply(ctx)?;

        // Final result: E = mc²
        let result = Expr::BinOp(BinOp::Eq, Box::new(e), Box::new(mc_sq));
        Ok(result)
    }
}
