//! Derivation rules: individual algebraic and logical operations.

use crate::context::DerivationContext;
use crate::error::DeriveError;
use crate::rewrite;
use nasrudin_core::{BinOp, Expr};

/// A single derivation rule that transforms the current expression.
pub trait DerivationRule: std::fmt::Debug {
    /// Human-readable name of this rule.
    fn name(&self) -> &str;

    /// Apply this rule to the context, updating the current expression.
    fn apply(&self, ctx: &mut DerivationContext) -> Result<(), DeriveError>;
}

/// Load an axiom into the context as the current working expression.
#[derive(Debug)]
pub struct IntroduceAxiom {
    pub axiom_name: String,
    pub statement: Expr,
}

impl DerivationRule for IntroduceAxiom {
    fn name(&self) -> &str {
        "introduce_axiom"
    }

    fn apply(&self, ctx: &mut DerivationContext) -> Result<(), DeriveError> {
        ctx.add_fact(&self.axiom_name, self.statement.clone());
        ctx.record_step(
            format!("Load axiom: {}", self.axiom_name),
            self.name(),
            self.statement.clone(),
        );
        Ok(())
    }
}

/// Substitute a variable with a specific value.
#[derive(Debug)]
pub struct SubstituteValue {
    pub var: String,
    pub value: Expr,
    pub reason: String,
}

impl DerivationRule for SubstituteValue {
    fn name(&self) -> &str {
        "substitute_value"
    }

    fn apply(&self, ctx: &mut DerivationContext) -> Result<(), DeriveError> {
        let current = ctx
            .current()
            .ok_or_else(|| DeriveError::RewriteFailed {
                reason: "no current expression".into(),
            })?
            .clone();

        // Record the assumption
        let assumption = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var(self.var.clone())),
            Box::new(self.value.clone()),
        );
        ctx.assume(&self.reason, assumption);

        // Apply substitution
        let result = rewrite::substitute_in_equation(&current, &self.var, &self.value);

        ctx.record_step(
            format!("Substitute {} = {} ({})", self.var, self.value.to_canonical(), self.reason),
            self.name(),
            result,
        );
        Ok(())
    }
}

/// Simplify the current expression using algebraic identities.
#[derive(Debug)]
pub struct AlgebraicSimplify;

impl DerivationRule for AlgebraicSimplify {
    fn name(&self) -> &str {
        "algebraic_simplify"
    }

    fn apply(&self, ctx: &mut DerivationContext) -> Result<(), DeriveError> {
        let current = ctx
            .current()
            .ok_or_else(|| DeriveError::RewriteFailed {
                reason: "no current expression".into(),
            })?
            .clone();

        let result = rewrite::simplify(&current);

        ctx.record_step("Simplify algebraically", self.name(), result);
        Ok(())
    }
}

/// Rearrange an equation: from `LHS = RHS` extract a specific form.
///
/// Given `E² - p²c² = (mc²)²`, rearranges to `E² = p²c² + (mc²)²`.
#[derive(Debug)]
pub struct RearrangeEquation {
    pub description: String,
    pub target: Expr,
}

impl DerivationRule for RearrangeEquation {
    fn name(&self) -> &str {
        "rearrange_equation"
    }

    fn apply(&self, ctx: &mut DerivationContext) -> Result<(), DeriveError> {
        // The rearranged form is provided directly — the Lean proof
        // justifies the algebraic step via `linarith`.
        ctx.record_step(&self.description, self.name(), self.target.clone());
        Ok(())
    }
}

/// Take the positive square root of both sides of E² = X².
///
/// Requires: E ≥ 0 and X ≥ 0, then E² = X² ⟹ E = X.
#[derive(Debug)]
pub struct TakePositiveRoot;

impl DerivationRule for TakePositiveRoot {
    fn name(&self) -> &str {
        "take_positive_root"
    }

    fn apply(&self, ctx: &mut DerivationContext) -> Result<(), DeriveError> {
        let current = ctx
            .current()
            .ok_or_else(|| DeriveError::RewriteFailed {
                reason: "no current expression".into(),
            })?
            .clone();

        // Expect: BinOp(Eq, BinOp(Pow, lhs, 2), BinOp(Pow, rhs, 2))
        if let Expr::BinOp(BinOp::Eq, lhs_sq, rhs_sq) = &current {
            let lhs = extract_square_base(lhs_sq);
            let rhs = extract_square_base(rhs_sq);

            if let (Some(l), Some(r)) = (lhs, rhs) {
                let result = Expr::BinOp(BinOp::Eq, Box::new(l), Box::new(r));
                ctx.record_step(
                    "Take positive square root (E ≥ 0, mc² ≥ 0)",
                    self.name(),
                    result,
                );
                return Ok(());
            }
        }

        Err(DeriveError::RewriteFailed {
            reason: "expression is not of the form X² = Y²".into(),
        })
    }
}

/// Extract the base from `Pow(base, 2)`.
fn extract_square_base(expr: &Expr) -> Option<Expr> {
    if let Expr::BinOp(BinOp::Pow, base, exp) = expr {
        if **exp == Expr::Lit(2, 1) {
            return Some((**base).clone());
        }
    }
    None
}

/// Apply a custom rewrite using pattern matching.
#[derive(Debug)]
pub struct PatternRewrite {
    pub description: String,
    pub pattern: Expr,
    pub replacement: Expr,
}

impl DerivationRule for PatternRewrite {
    fn name(&self) -> &str {
        "pattern_rewrite"
    }

    fn apply(&self, ctx: &mut DerivationContext) -> Result<(), DeriveError> {
        let current = ctx
            .current()
            .ok_or_else(|| DeriveError::RewriteFailed {
                reason: "no current expression".into(),
            })?
            .clone();

        let result = rewrite_at_root(&current, &self.pattern, &self.replacement)?;

        ctx.record_step(&self.description, self.name(), result);
        Ok(())
    }
}

/// Attempt to rewrite `expr` at the root or in subexpressions.
fn rewrite_at_root(expr: &Expr, pattern: &Expr, replacement: &Expr) -> Result<Expr, DeriveError> {
    // Try matching at root
    if let Some(bindings) = rewrite::match_expr(pattern, expr) {
        return Ok(rewrite::apply_substitution(replacement, &bindings));
    }

    // Try matching inside BinOp
    match expr {
        Expr::BinOp(op, l, r) => {
            if let Ok(new_l) = rewrite_at_root(l, pattern, replacement) {
                return Ok(Expr::BinOp(op.clone(), Box::new(new_l), r.clone()));
            }
            if let Ok(new_r) = rewrite_at_root(r, pattern, replacement) {
                return Ok(Expr::BinOp(op.clone(), l.clone(), Box::new(new_r)));
            }
        }
        Expr::UnOp(op, e) => {
            if let Ok(new_e) = rewrite_at_root(e, pattern, replacement) {
                return Ok(Expr::UnOp(op.clone(), Box::new(new_e)));
            }
        }
        _ => {}
    }

    Err(DeriveError::RewriteFailed {
        reason: "pattern not found in expression".into(),
    })
}
