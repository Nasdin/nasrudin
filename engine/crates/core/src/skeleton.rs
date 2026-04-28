//! Canonicalise an `Expr` into a goal-skeleton suitable for cache lookup.
//!
//! Two expressions hash to the same skeleton iff they differ only in:
//!   - literal numeric values (every `Lit` erased to `L`)
//!   - free-variable names (renamed `V0`, `V1`, … in left-to-right discovery order)
//!
//! Operator structure, constants (`Const`), and bound-variable names inside
//! `Lam` / `Pi` / `Let` / `Deriv` / `Integral` / `Sum` / `Prod` / `Limit`
//! are flattened away (bound names don't affect skeleton — alpha-equivalence).
//!
//! Used by the tactic-priors cache: similar-shaped goals share a hash so a
//! tactic chain that proved one goal is tried first on the next.

use crate::expr::{BinOp, Expr, PhysConst, UnOp};
use std::collections::HashMap;

/// 8-byte BLAKE3 prefix over the skeleton's canonical bytes.
pub type SkeletonHash = [u8; 8];

/// Render the canonical skeleton string. Public for debugging.
pub fn normalise_to_skeleton(expr: &Expr) -> String {
    let mut out = String::new();
    let mut var_map: HashMap<String, usize> = HashMap::new();
    walk(expr, &mut out, &mut var_map);
    out
}

/// 8-byte BLAKE3 prefix over the skeleton string.
pub fn skeleton_hash(expr: &Expr) -> SkeletonHash {
    let s = normalise_to_skeleton(expr);
    let h = blake3::hash(s.as_bytes());
    let mut out = [0u8; 8];
    out.copy_from_slice(&h.as_bytes()[..8]);
    out
}

fn walk(expr: &Expr, out: &mut String, var_map: &mut HashMap<String, usize>) {
    match expr {
        Expr::Var(name) => {
            let idx = match var_map.get(name) {
                Some(i) => *i,
                None => {
                    let i = var_map.len();
                    var_map.insert(name.clone(), i);
                    i
                }
            };
            out.push_str(&format!("V{idx}"));
        }
        Expr::Const(c) => {
            out.push_str("C:");
            out.push_str(const_name(c));
        }
        Expr::Lit(_, _) => out.push('L'),
        Expr::App(f, x) => {
            out.push_str("(@ ");
            walk(f, out, var_map);
            out.push(' ');
            walk(x, out, var_map);
            out.push(')');
        }
        // Bound-variable names are intentionally erased — alpha-equivalence
        // means two lambdas differing only in their parameter name should
        // share a skeleton.
        Expr::Lam(_, ty, body) => {
            out.push_str("(lam ");
            walk(ty, out, var_map);
            out.push(' ');
            walk(body, out, var_map);
            out.push(')');
        }
        Expr::Pi(_, ty, body) => {
            out.push_str("(pi ");
            walk(ty, out, var_map);
            out.push(' ');
            walk(body, out, var_map);
            out.push(')');
        }
        Expr::BinOp(op, l, r) => {
            out.push('(');
            out.push_str(binop_name(op));
            out.push(' ');
            walk(l, out, var_map);
            out.push(' ');
            walk(r, out, var_map);
            out.push(')');
        }
        Expr::UnOp(op, e) => {
            out.push('(');
            out.push_str(unop_name(op));
            out.push(' ');
            walk(e, out, var_map);
            out.push(')');
        }
        Expr::Deriv(e, _) => {
            out.push_str("(deriv ");
            walk(e, out, var_map);
            out.push(')');
        }
        Expr::PartialDeriv(e, _) => {
            out.push_str("(pderiv ");
            walk(e, out, var_map);
            out.push(')');
        }
        Expr::Integral {
            body, lower, upper, ..
        } => {
            out.push_str("(int ");
            walk(body, out, var_map);
            if let Some(l) = lower {
                out.push(' ');
                walk(l, out, var_map);
            }
            if let Some(u) = upper {
                out.push(' ');
                walk(u, out, var_map);
            }
            out.push(')');
        }
        Expr::Sum {
            body, lower, upper, ..
        } => {
            out.push_str("(sum ");
            walk(body, out, var_map);
            out.push(' ');
            walk(lower, out, var_map);
            out.push(' ');
            walk(upper, out, var_map);
            out.push(')');
        }
        Expr::Prod {
            body, lower, upper, ..
        } => {
            out.push_str("(prod ");
            walk(body, out, var_map);
            out.push(' ');
            walk(lower, out, var_map);
            out.push(' ');
            walk(upper, out, var_map);
            out.push(')');
        }
        Expr::Limit {
            body, approaching, ..
        } => {
            out.push_str("(lim ");
            walk(body, out, var_map);
            out.push(' ');
            walk(approaching, out, var_map);
            out.push(')');
        }
        Expr::Let(_, val, body) => {
            out.push_str("(let ");
            walk(val, out, var_map);
            out.push(' ');
            walk(body, out, var_map);
            out.push(')');
        }
    }
}

fn binop_name(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Pow => "^",
        BinOp::Eq => "=",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Implies => "->",
        BinOp::Iff => "<->",
        BinOp::Cross => "cross",
        BinOp::Dot => "dot",
        BinOp::TensorProduct => "tensor",
    }
}

fn unop_name(op: &UnOp) -> &'static str {
    match op {
        UnOp::Neg => "neg",
        UnOp::Abs => "abs",
        UnOp::Sqrt => "sqrt",
        UnOp::Sin => "sin",
        UnOp::Cos => "cos",
        UnOp::Tan => "tan",
        UnOp::Exp => "exp",
        UnOp::Log => "log",
        UnOp::Ln => "ln",
        UnOp::Grad => "grad",
        UnOp::Div => "div",
        UnOp::Curl => "curl",
        UnOp::Laplacian => "laplacian",
        UnOp::Transpose => "transpose",
        UnOp::Conjugate => "conjugate",
        UnOp::Trace => "trace",
        UnOp::Det => "det",
    }
}

fn const_name(c: &PhysConst) -> &'static str {
    match c {
        PhysConst::SpeedOfLight => "c",
        PhysConst::PlanckConst => "h",
        PhysConst::ReducedPlanck => "hbar",
        PhysConst::GravConst => "G",
        PhysConst::Boltzmann => "kB",
        PhysConst::ElectronCharge => "e",
        PhysConst::ElectronMass => "me",
        PhysConst::ProtonMass => "mp",
        PhysConst::VacuumPermittivity => "eps0",
        PhysConst::VacuumPermeability => "mu0",
        PhysConst::Avogadro => "NA",
        PhysConst::Pi => "pi",
        PhysConst::EulersNumber => "E",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{BinOp, Expr};

    #[test]
    fn literal_numerals_collide() {
        let e1 = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Lit(5, 1)),
        );
        let e2 = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Lit(7, 1)),
        );
        assert_eq!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn alpha_renamed_variables_collide() {
        let e1 = Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        let e2 = Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Var("y".into())),
        );
        assert_eq!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn different_operators_diverge() {
        let e1 = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Var("y".into())),
        );
        let e2 = Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Var("y".into())),
        );
        assert_ne!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn sub_swap_collides_under_normalisation() {
        // (a - b) and (b - a) both rename to (- V0 V1) — they DO collide.
        // This is intentional: priors care about expression *shape*, not
        // whether the operands happen to be in the same originally-named order.
        let e1 = Expr::BinOp(
            BinOp::Sub,
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        let e2 = Expr::BinOp(
            BinOp::Sub,
            Box::new(Expr::Var("b".into())),
            Box::new(Expr::Var("a".into())),
        );
        assert_eq!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn deterministic() {
        let e = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Lit(3, 1)),
        );
        assert_eq!(skeleton_hash(&e), skeleton_hash(&e));
    }

    #[test]
    fn different_constants_diverge() {
        let e1 = Expr::Const(PhysConst::SpeedOfLight);
        let e2 = Expr::Const(PhysConst::PlanckConst);
        assert_ne!(skeleton_hash(&e1), skeleton_hash(&e2));
    }
}
