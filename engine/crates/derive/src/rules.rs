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
///
/// **Soundness gate (P-Task 12):** rejects unless `var = value` is
/// already an established fact in the chain context — either an axiom
/// the chain has introduced or a hypothesis recorded by an earlier
/// rule. Without this gate the rule would happily substitute any
/// claimed value, producing chains where chain-replay accepts but
/// `linarith` in the emitted Lean fails because the assumption was
/// never derived. Now: chain replay rejects unsound substitutions
/// at the source, so by the time a chain reaches the server it's
/// guaranteed that the substitution is justified.
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

        // Soundness gate: walk every known fact + assumption in ctx
        // looking for one of:  `var = value`,  `value = var`
        // (canonically equivalent under `Eq`'s symmetry). Without a
        // matching fact we have no proof basis for the substitution
        // and Lean would reject the resulting chain. Reject early so
        // workers never submit unsound substitutions in the first place.
        let var_canon = Expr::Var(self.var.clone()).to_canonical();
        let val_canon = self.value.to_canonical();
        let mut justification_found = false;
        let candidates = ctx.facts().iter().chain(ctx.assumptions().iter());
        for (_label, fact) in candidates {
            if let Expr::BinOp(BinOp::Eq, l, r) = fact {
                let l_canon = l.to_canonical();
                let r_canon = r.to_canonical();
                if (l_canon == var_canon && r_canon == val_canon)
                    || (l_canon == val_canon && r_canon == var_canon)
                {
                    justification_found = true;
                    break;
                }
            }
        }
        if !justification_found {
            return Err(DeriveError::RewriteFailed {
                reason: format!(
                    "SubstituteValue {{var: {}, value: {}}} not justified by any chain fact",
                    self.var,
                    self.value.to_canonical()
                ),
            });
        }

        // Record the assumption (now provably derivable from facts)
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
///
/// **No soundness gate at chain replay** (P-Task 12 final design):
/// the worker's local lake build IS the soundness oracle. We
/// considered pattern-matching valid rearrangements (swap / square /
/// negate / simplify-equivalent) but rejected that approach because
/// it would block genuinely novel rearrangements that Lean's tactics
/// (`nlinarith`/`polyrith`/`ring`) can prove but our pattern set
/// can't enumerate. The product mission is to discover physics
/// theorems mankind doesn't yet know — we cannot pre-restrict the
/// search to algebraic moves we already know about.
///
/// Trade: the chain replay is *structurally* sound (the rule produces
/// a well-formed Expr) but the *mathematical* claim is verified by
/// the worker's local lake build before submission, and again lazily
/// by the server's lake build on download. Bad rearrangements get
/// caught by the kernel, not by us.
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
        // Record the claimed target. Lean's tactics judge soundness
        // at lake-build time — chain replay just needs the structural
        // sequence so the emitter can produce well-formed Lean source.
        ctx.record_step(&self.description, self.name(), self.target.clone());
        Ok(())
    }
}

/// Take the positive square root of both sides of E² = X².
///
/// Requires: E ≥ 0 and X ≥ 0, then E² = X² ⟹ E = X.
///
/// **Soundness gate (P-Task 12):** rejects unless ctx contains
/// non-negativity facts for both bases — i.e. for `LHS² = RHS²`,
/// there must be facts `0 ≤ LHS` (or `LHS ≥ 0`, or `LHS > 0`) and
/// the same for RHS. Without those, the rule is unsound — `(-1)² =
/// 1²` is true but `-1 ≠ 1`. By gating at chain-replay time we
/// guarantee the emitted Lean proof's `Real.sqrt_sq` invocation
/// has the positivity hypotheses it needs to discharge.
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
                // Require non-negativity facts for both bases.
                if !has_nonneg_fact(ctx, &l) {
                    return Err(DeriveError::RewriteFailed {
                        reason: format!(
                            "TakePositiveRoot: no non-negativity fact for LHS base `{}`",
                            l.to_canonical()
                        ),
                    });
                }
                if !has_nonneg_fact(ctx, &r) {
                    return Err(DeriveError::RewriteFailed {
                        reason: format!(
                            "TakePositiveRoot: no non-negativity fact for RHS base `{}`",
                            r.to_canonical()
                        ),
                    });
                }
                let result = Expr::BinOp(BinOp::Eq, Box::new(l), Box::new(r));
                ctx.record_step(
                    "Take positive square root (LHS ≥ 0, RHS ≥ 0 from ctx)",
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

/// Look for a fact in `ctx` matching `expr ≥ 0`, `expr > 0`, or
/// equivalent forms. Used by [`TakePositiveRoot`] to ensure the
/// implicit non-negativity precondition holds before applying.
fn has_nonneg_fact(ctx: &DerivationContext, expr: &Expr) -> bool {
    let target_canon = expr.to_canonical();
    let zero = Expr::Lit(0, 1);
    let candidates = ctx.facts().iter().chain(ctx.assumptions().iter());
    for (_label, fact) in candidates {
        match fact {
            // `expr ≥ 0` or `expr > 0`
            Expr::BinOp(BinOp::Ge, l, r) | Expr::BinOp(BinOp::Gt, l, r) => {
                if l.to_canonical() == target_canon && **r == zero {
                    return true;
                }
            }
            // `0 ≤ expr` or `0 < expr`
            Expr::BinOp(BinOp::Le, l, r) | Expr::BinOp(BinOp::Lt, l, r) => {
                if **l == zero && r.to_canonical() == target_canon {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
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
