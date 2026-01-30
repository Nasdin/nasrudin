//! Expression pattern matching and rewriting.
//!
//! Provides substitution, simplification, and pattern matching over `Expr` trees.

use nasrudin_core::{BinOp, Expr};
use std::collections::HashMap;

/// A substitution map from variable names to replacement expressions.
pub type Substitution = HashMap<String, Expr>;

/// Check if `expr` matches `pattern`, producing a substitution map.
///
/// Pattern variables (any `Var`) in the pattern can match any sub-expression.
/// Literal, constant, and structural nodes must match exactly.
pub fn match_expr(pattern: &Expr, expr: &Expr) -> Option<Substitution> {
    let mut bindings = Substitution::new();
    if match_recursive(pattern, expr, &mut bindings) {
        Some(bindings)
    } else {
        None
    }
}

fn match_recursive(pattern: &Expr, expr: &Expr, bindings: &mut Substitution) -> bool {
    match pattern {
        // Pattern variable: matches anything, but must be consistent
        Expr::Var(name) => {
            if let Some(existing) = bindings.get(name) {
                existing == expr
            } else {
                bindings.insert(name.clone(), expr.clone());
                true
            }
        }
        // Structural matching
        Expr::Const(pc) => matches!(expr, Expr::Const(ec) if pc == ec),
        Expr::Lit(pn, pd) => matches!(expr, Expr::Lit(en, ed) if pn == en && pd == ed),
        Expr::BinOp(pop, pl, pr) => {
            if let Expr::BinOp(eop, el, er) = expr {
                pop == eop
                    && match_recursive(pl, el, bindings)
                    && match_recursive(pr, er, bindings)
            } else {
                false
            }
        }
        Expr::UnOp(pop, pe) => {
            if let Expr::UnOp(eop, ee) = expr {
                pop == eop && match_recursive(pe, ee, bindings)
            } else {
                false
            }
        }
        Expr::App(pf, px) => {
            if let Expr::App(ef, ex) = expr {
                match_recursive(pf, ef, bindings) && match_recursive(px, ex, bindings)
            } else {
                false
            }
        }
        // For other node types, require exact equality
        _ => pattern == expr,
    }
}

/// Apply a substitution to an expression, replacing variables with their bindings.
pub fn apply_substitution(expr: &Expr, subst: &Substitution) -> Expr {
    match expr {
        Expr::Var(name) => {
            if let Some(replacement) = subst.get(name) {
                replacement.clone()
            } else {
                expr.clone()
            }
        }
        Expr::Const(_) | Expr::Lit(_, _) => expr.clone(),
        Expr::BinOp(op, l, r) => Expr::BinOp(
            op.clone(),
            Box::new(apply_substitution(l, subst)),
            Box::new(apply_substitution(r, subst)),
        ),
        Expr::UnOp(op, e) => {
            Expr::UnOp(op.clone(), Box::new(apply_substitution(e, subst)))
        }
        Expr::App(f, x) => Expr::App(
            Box::new(apply_substitution(f, subst)),
            Box::new(apply_substitution(x, subst)),
        ),
        Expr::Lam(var, ty, body) => Expr::Lam(
            var.clone(),
            Box::new(apply_substitution(ty, subst)),
            Box::new(apply_substitution(body, subst)),
        ),
        Expr::Pi(var, a, b) => Expr::Pi(
            var.clone(),
            Box::new(apply_substitution(a, subst)),
            Box::new(apply_substitution(b, subst)),
        ),
        Expr::Deriv(e, var) => {
            Expr::Deriv(Box::new(apply_substitution(e, subst)), var.clone())
        }
        Expr::PartialDeriv(e, var) => {
            Expr::PartialDeriv(Box::new(apply_substitution(e, subst)), var.clone())
        }
        Expr::Integral {
            body,
            var,
            lower,
            upper,
        } => Expr::Integral {
            body: Box::new(apply_substitution(body, subst)),
            var: var.clone(),
            lower: lower.as_ref().map(|e| Box::new(apply_substitution(e, subst))),
            upper: upper.as_ref().map(|e| Box::new(apply_substitution(e, subst))),
        },
        Expr::Sum {
            body,
            var,
            lower,
            upper,
        } => Expr::Sum {
            body: Box::new(apply_substitution(body, subst)),
            var: var.clone(),
            lower: Box::new(apply_substitution(lower, subst)),
            upper: Box::new(apply_substitution(upper, subst)),
        },
        Expr::Limit {
            body,
            var,
            approaching,
        } => Expr::Limit {
            body: Box::new(apply_substitution(body, subst)),
            var: var.clone(),
            approaching: Box::new(apply_substitution(approaching, subst)),
        },
        Expr::Let(var, val, body) => Expr::Let(
            var.clone(),
            Box::new(apply_substitution(val, subst)),
            Box::new(apply_substitution(body, subst)),
        ),
    }
}

/// Simplify an expression using algebraic identities.
///
/// Applied rules:
/// - `0 + x → x`, `x + 0 → x`
/// - `0 * x → 0`, `x * 0 → 0`
/// - `1 * x → x`, `x * 1 → x`
/// - `x ^ 0 → 1`, `x ^ 1 → x`
/// - `0 ^ n → 0` (for n > 0)
/// - `x - 0 → x`
/// - Literal arithmetic: `Lit(a) op Lit(b) → Lit(result)`
pub fn simplify(expr: &Expr) -> Expr {
    // Bottom-up: simplify children first, then apply rules at this node
    let simplified = match expr {
        Expr::BinOp(op, l, r) => {
            let sl = simplify(l);
            let sr = simplify(r);
            simplify_binop(op, &sl, &sr)
        }
        Expr::UnOp(op, e) => {
            let se = simplify(e);
            simplify_unop(op, &se)
        }
        _ => expr.clone(),
    };
    simplified
}

fn is_zero(e: &Expr) -> bool {
    matches!(e, Expr::Lit(0, _))
}

fn is_one(e: &Expr) -> bool {
    matches!(e, Expr::Lit(1, 1))
}

fn zero() -> Expr {
    Expr::Lit(0, 1)
}

fn one() -> Expr {
    Expr::Lit(1, 1)
}

fn simplify_binop(op: &BinOp, l: &Expr, r: &Expr) -> Expr {
    match op {
        BinOp::Add => {
            if is_zero(l) {
                return r.clone();
            }
            if is_zero(r) {
                return l.clone();
            }
            // Literal addition
            if let (Expr::Lit(ln, ld), Expr::Lit(rn, rd)) = (l, r) {
                if ld == rd {
                    return Expr::Lit(ln + rn, *ld);
                }
                // Cross multiply for different denominators
                let num = ln * (*rd as i64) + rn * (*ld as i64);
                let den = ld * rd;
                return Expr::Lit(num, den);
            }
        }
        BinOp::Sub => {
            if is_zero(r) {
                return l.clone();
            }
            if l == r {
                return zero();
            }
        }
        BinOp::Mul => {
            if is_zero(l) || is_zero(r) {
                return zero();
            }
            if is_one(l) {
                return r.clone();
            }
            if is_one(r) {
                return l.clone();
            }
            // Literal multiplication
            if let (Expr::Lit(ln, ld), Expr::Lit(rn, rd)) = (l, r) {
                return Expr::Lit(ln * rn, ld * rd);
            }
        }
        BinOp::Pow => {
            if is_zero(r) {
                return one();
            }
            if is_one(r) {
                return l.clone();
            }
            if is_zero(l) {
                // 0^n = 0 for n > 0 (we assume positive exponents here)
                if !is_zero(r) {
                    return zero();
                }
            }
        }
        BinOp::Div => {
            if is_zero(l) {
                return zero();
            }
            if is_one(r) {
                return l.clone();
            }
        }
        _ => {}
    }
    // No simplification applied
    Expr::BinOp(op.clone(), Box::new(l.clone()), Box::new(r.clone()))
}

fn simplify_unop(op: &nasrudin_core::UnOp, e: &Expr) -> Expr {
    match op {
        nasrudin_core::UnOp::Neg => {
            if is_zero(e) {
                return zero();
            }
            // Double negation
            if let Expr::UnOp(nasrudin_core::UnOp::Neg, inner) = e {
                return (**inner).clone();
            }
        }
        _ => {}
    }
    Expr::UnOp(op.clone(), Box::new(e.clone()))
}

/// Substitute a specific variable with a value in an equation expression.
///
/// If `expr` is `BinOp(Eq, lhs, rhs)`, substitutes in both sides.
pub fn substitute_in_equation(expr: &Expr, var: &str, value: &Expr) -> Expr {
    let mut subst = Substitution::new();
    subst.insert(var.to_string(), value.clone());
    apply_substitution(expr, &subst)
}
