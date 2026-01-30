//! Mutation operators for `Expr` trees.
//!
//! Eight mutation operators that introduce controlled variation:
//! VarSwap, OpSwap, AxiomInjection, Simplify, UnaryWrap, UnaryUnwrap,
//! LitPerturb, ConstSwap.

use nasrudin_core::{BinOp, Expr, PhysConst, UnOp};
use rand::Rng;

/// Which mutation operator to apply.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MutationOp {
    /// Swap a variable name with another from the domain vocabulary.
    VarSwap,
    /// Replace a binary operator with a different one.
    OpSwap,
    /// Insert a physics axiom fragment as a subtree.
    AxiomInjection,
    /// Simplify: fold constant subexpressions.
    Simplify,
    /// Wrap a subtree with a unary operator.
    UnaryWrap,
    /// Remove a unary operator, exposing its child.
    UnaryUnwrap,
    /// Perturb a literal value by a small amount.
    LitPerturb,
    /// Swap one physical constant for another.
    ConstSwap,
}

const ALL_MUTATIONS: &[MutationOp] = &[
    MutationOp::VarSwap,
    MutationOp::OpSwap,
    MutationOp::AxiomInjection,
    MutationOp::Simplify,
    MutationOp::UnaryWrap,
    MutationOp::UnaryUnwrap,
    MutationOp::LitPerturb,
    MutationOp::ConstSwap,
];

/// Apply a random mutation to an expression.
pub fn mutate(expr: &Expr, rng: &mut impl Rng) -> Expr {
    let op = ALL_MUTATIONS[rng.random_range(0..ALL_MUTATIONS.len())];
    apply_mutation(expr, op, rng)
}

/// Apply a specific mutation operator.
pub fn apply_mutation(expr: &Expr, op: MutationOp, rng: &mut impl Rng) -> Expr {
    match op {
        MutationOp::VarSwap => var_swap(expr, rng),
        MutationOp::OpSwap => op_swap(expr, rng),
        MutationOp::AxiomInjection => axiom_injection(expr, rng),
        MutationOp::Simplify => simplify(expr),
        MutationOp::UnaryWrap => unary_wrap(expr, rng),
        MutationOp::UnaryUnwrap => unary_unwrap(expr),
        MutationOp::LitPerturb => lit_perturb(expr, rng),
        MutationOp::ConstSwap => const_swap(expr, rng),
    }
}

/// Domain-relevant variable names for physics.
const PHYSICS_VARS: &[&str] = &[
    "E", "m", "c", "p", "v", "t", "F", "a", "x", "r", "T", "S", "k", "h", "q", "V", "I", "R",
    "B", "G", "L", "H", "U", "W", "P", "n", "f", "omega", "lambda", "phi", "theta", "rho",
    "sigma",
];

/// Swap a random variable with a different one from the physics vocabulary.
fn var_swap(expr: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::Var(name) => {
            let new_name = loop {
                let candidate = PHYSICS_VARS[rng.random_range(0..PHYSICS_VARS.len())];
                if candidate != name {
                    break candidate.to_string();
                }
            };
            Expr::Var(new_name)
        }
        Expr::BinOp(op, l, r) => {
            if rng.random_bool(0.5) {
                Expr::BinOp(op.clone(), Box::new(var_swap(l, rng)), r.clone())
            } else {
                Expr::BinOp(op.clone(), l.clone(), Box::new(var_swap(r, rng)))
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(var_swap(e, rng))),
        other => other.clone(),
    }
}

/// Algebraic binary ops suitable for swapping.
const ALGEBRAIC_OPS: &[BinOp] = &[
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::Div,
    BinOp::Pow,
];

/// Replace a binary operator with a different one.
fn op_swap(expr: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::BinOp(op, l, r) => {
            if ALGEBRAIC_OPS.contains(op) {
                let new_op = loop {
                    let candidate = &ALGEBRAIC_OPS[rng.random_range(0..ALGEBRAIC_OPS.len())];
                    if candidate != op {
                        break candidate.clone();
                    }
                };
                Expr::BinOp(new_op, l.clone(), r.clone())
            } else {
                // Recurse into children
                if rng.random_bool(0.5) {
                    Expr::BinOp(op.clone(), Box::new(op_swap(l, rng)), r.clone())
                } else {
                    Expr::BinOp(op.clone(), l.clone(), Box::new(op_swap(r, rng)))
                }
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(op_swap(e, rng))),
        other => other.clone(),
    }
}

/// Inject a small axiom-like fragment into the tree.
fn axiom_injection(expr: &Expr, rng: &mut impl Rng) -> Expr {
    // Axiom fragments: common physics subexpressions
    let fragments = [
        // mc^2
        Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("m".into())),
            Box::new(Expr::BinOp(
                BinOp::Pow,
                Box::new(Expr::Const(PhysConst::SpeedOfLight)),
                Box::new(Expr::Lit(2, 1)),
            )),
        ),
        // hbar * omega
        Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Const(PhysConst::ReducedPlanck)),
            Box::new(Expr::Var("omega".into())),
        ),
        // k_B * T
        Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Const(PhysConst::Boltzmann)),
            Box::new(Expr::Var("T".into())),
        ),
        // p^2 / (2m)
        Expr::BinOp(
            BinOp::Div,
            Box::new(Expr::BinOp(
                BinOp::Pow,
                Box::new(Expr::Var("p".into())),
                Box::new(Expr::Lit(2, 1)),
            )),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Lit(2, 1)),
                Box::new(Expr::Var("m".into())),
            )),
        ),
    ];

    let fragment = &fragments[rng.random_range(0..fragments.len())];

    // Replace a random leaf node with the fragment
    replace_random_leaf(expr, fragment, rng)
}

/// Replace a random leaf in the expression with a replacement subtree.
fn replace_random_leaf(expr: &Expr, replacement: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::Var(_) | Expr::Const(_) | Expr::Lit(_, _) => {
            // This is a leaf; replace with some probability
            if rng.random_bool(0.3) {
                replacement.clone()
            } else {
                expr.clone()
            }
        }
        Expr::BinOp(op, l, r) => {
            if rng.random_bool(0.5) {
                Expr::BinOp(
                    op.clone(),
                    Box::new(replace_random_leaf(l, replacement, rng)),
                    r.clone(),
                )
            } else {
                Expr::BinOp(
                    op.clone(),
                    l.clone(),
                    Box::new(replace_random_leaf(r, replacement, rng)),
                )
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(
            op.clone(),
            Box::new(replace_random_leaf(e, replacement, rng)),
        ),
        other => other.clone(),
    }
}

/// Simplify: fold trivial constant subexpressions.
fn simplify(expr: &Expr) -> Expr {
    match expr {
        // x + 0 => x, 0 + x => x
        Expr::BinOp(BinOp::Add, l, r) => {
            if matches!(r.as_ref(), Expr::Lit(0, _)) {
                simplify(l)
            } else if matches!(l.as_ref(), Expr::Lit(0, _)) {
                simplify(r)
            } else {
                Expr::BinOp(BinOp::Add, Box::new(simplify(l)), Box::new(simplify(r)))
            }
        }
        // x * 1 => x, 1 * x => x
        Expr::BinOp(BinOp::Mul, l, r) => {
            if matches!(r.as_ref(), Expr::Lit(1, 1)) {
                simplify(l)
            } else if matches!(l.as_ref(), Expr::Lit(1, 1)) {
                simplify(r)
            } else if matches!(r.as_ref(), Expr::Lit(0, _)) || matches!(l.as_ref(), Expr::Lit(0, _))
            {
                Expr::Lit(0, 1)
            } else {
                Expr::BinOp(BinOp::Mul, Box::new(simplify(l)), Box::new(simplify(r)))
            }
        }
        // x ^ 1 => x, x ^ 0 => 1
        Expr::BinOp(BinOp::Pow, l, r) => {
            if matches!(r.as_ref(), Expr::Lit(1, 1)) {
                simplify(l)
            } else if matches!(r.as_ref(), Expr::Lit(0, _)) {
                Expr::Lit(1, 1)
            } else {
                Expr::BinOp(BinOp::Pow, Box::new(simplify(l)), Box::new(simplify(r)))
            }
        }
        // Double negation: --x => x
        Expr::UnOp(UnOp::Neg, inner) => {
            if let Expr::UnOp(UnOp::Neg, e) = inner.as_ref() {
                simplify(e)
            } else {
                Expr::UnOp(UnOp::Neg, Box::new(simplify(inner)))
            }
        }
        Expr::BinOp(op, l, r) => {
            Expr::BinOp(op.clone(), Box::new(simplify(l)), Box::new(simplify(r)))
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(simplify(e))),
        other => other.clone(),
    }
}

/// Unary operators suitable for wrapping.
const WRAP_OPS: &[UnOp] = &[
    UnOp::Neg,
    UnOp::Abs,
    UnOp::Sqrt,
    UnOp::Exp,
    UnOp::Ln,
];

/// Wrap a random subtree with a unary operator.
fn unary_wrap(expr: &Expr, rng: &mut impl Rng) -> Expr {
    let op = &WRAP_OPS[rng.random_range(0..WRAP_OPS.len())];
    // Wrap the whole expression with some probability, or recurse
    if rng.random_bool(0.4) {
        Expr::UnOp(op.clone(), Box::new(expr.clone()))
    } else {
        match expr {
            Expr::BinOp(bop, l, r) => {
                if rng.random_bool(0.5) {
                    Expr::BinOp(bop.clone(), Box::new(unary_wrap(l, rng)), r.clone())
                } else {
                    Expr::BinOp(bop.clone(), l.clone(), Box::new(unary_wrap(r, rng)))
                }
            }
            _ => Expr::UnOp(op.clone(), Box::new(expr.clone())),
        }
    }
}

/// Remove a unary operator, exposing its child directly.
fn unary_unwrap(expr: &Expr) -> Expr {
    match expr {
        Expr::UnOp(_, e) => *e.clone(),
        Expr::BinOp(op, l, r) => {
            // Try to unwrap in left or right child
            Expr::BinOp(
                op.clone(),
                Box::new(unary_unwrap(l)),
                Box::new(unary_unwrap(r)),
            )
        }
        other => other.clone(),
    }
}

/// Perturb a literal value by a small integer offset or ratio change.
fn lit_perturb(expr: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::Lit(n, d) => {
            let delta: i64 = rng.random_range(-2..=2);
            let new_n = n.saturating_add(delta);
            // Keep denominator positive
            let new_d = if *d == 0 { 1 } else { *d };
            Expr::Lit(new_n, new_d)
        }
        Expr::BinOp(op, l, r) => {
            if rng.random_bool(0.5) {
                Expr::BinOp(op.clone(), Box::new(lit_perturb(l, rng)), r.clone())
            } else {
                Expr::BinOp(op.clone(), l.clone(), Box::new(lit_perturb(r, rng)))
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(lit_perturb(e, rng))),
        other => other.clone(),
    }
}

/// All physical constants for swapping.
const ALL_CONSTS: &[PhysConst] = &[
    PhysConst::SpeedOfLight,
    PhysConst::PlanckConst,
    PhysConst::ReducedPlanck,
    PhysConst::GravConst,
    PhysConst::Boltzmann,
    PhysConst::ElectronCharge,
    PhysConst::ElectronMass,
    PhysConst::ProtonMass,
    PhysConst::Pi,
];

/// Swap a physical constant with a different one.
fn const_swap(expr: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::Const(c) => {
            let new_const = loop {
                let candidate = &ALL_CONSTS[rng.random_range(0..ALL_CONSTS.len())];
                if candidate != c {
                    break candidate.clone();
                }
            };
            Expr::Const(new_const)
        }
        Expr::BinOp(op, l, r) => {
            if rng.random_bool(0.5) {
                Expr::BinOp(op.clone(), Box::new(const_swap(l, rng)), r.clone())
            } else {
                Expr::BinOp(op.clone(), l.clone(), Box::new(const_swap(r, rng)))
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(const_swap(e, rng))),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simplify_add_zero() {
        let expr = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Lit(0, 1)),
        );
        let result = simplify(&expr);
        assert_eq!(result, Expr::Var("x".into()));
    }

    #[test]
    fn simplify_mul_one() {
        let expr = Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Lit(1, 1)),
            Box::new(Expr::Var("y".into())),
        );
        let result = simplify(&expr);
        assert_eq!(result, Expr::Var("y".into()));
    }

    #[test]
    fn simplify_pow_zero() {
        let expr = Expr::BinOp(
            BinOp::Pow,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Lit(0, 1)),
        );
        let result = simplify(&expr);
        assert_eq!(result, Expr::Lit(1, 1));
    }

    #[test]
    fn mutate_produces_different_expr() {
        let expr = Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("m".into())),
            Box::new(Expr::Var("a".into())),
        );
        let mut rng = rand::rng();
        // Run mutation multiple times; at least one should differ
        let mut found_different = false;
        for _ in 0..20 {
            let mutated = mutate(&expr, &mut rng);
            if mutated != expr {
                found_different = true;
                break;
            }
        }
        assert!(found_different, "Mutation should produce different expressions");
    }
}
