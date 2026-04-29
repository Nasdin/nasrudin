//! Canonicalise an `Expr` into a goal-skeleton suitable for cache lookup.
//!
//! Two expressions hash to the same skeleton iff they differ only in:
//!   - literal numeric values (every `Lit` erased to `L`)
//!   - free-variable names (renamed `V0`, `V1`, … in left-to-right discovery order)
//!   - bound-variable names (renamed `B0`, `B1`, … per binder scope — alpha-equivalence)
//!
//! Operator structure, constants (`Const`), and the *presence* of binders
//! are part of the skeleton: `(λx. x) + y` and `(λx. y) + x` diverge,
//! but `λx. x` and `λy. y` collide.
//!
//! Used by the tactic-priors cache: similar-shaped goals share a hash so a
//! tactic chain that proved one goal is tried first on the next.

use crate::expr::{BinOp, Expr, PhysConst, UnOp};
use std::collections::HashMap;
use std::fmt::Write;

/// 8-byte BLAKE3 prefix over the skeleton's canonical bytes.
pub type SkeletonHash = [u8; 8];

/// Render the canonical skeleton string. Public for debugging.
pub fn normalise_to_skeleton(expr: &Expr) -> String {
    let mut out = String::new();
    let mut free_vars: HashMap<String, usize> = HashMap::new();
    let mut bound_stack: Vec<HashMap<String, usize>> = Vec::new();
    let mut next_bound: usize = 0;
    walk(
        expr,
        &mut out,
        &mut free_vars,
        &mut bound_stack,
        &mut next_bound,
    );
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

fn walk(
    expr: &Expr,
    out: &mut String,
    free_vars: &mut HashMap<String, usize>,
    bound_stack: &mut Vec<HashMap<String, usize>>,
    next_bound: &mut usize,
) {
    match expr {
        Expr::Var(name) => {
            // Bound vars shadow free — search innermost scope first.
            for scope in bound_stack.iter().rev() {
                if let Some(&bidx) = scope.get(name) {
                    write!(out, "B{bidx}").unwrap();
                    return;
                }
            }
            // Free var.
            let idx = match free_vars.get(name) {
                Some(&i) => i,
                None => {
                    let i = free_vars.len();
                    free_vars.insert(name.clone(), i);
                    i
                }
            };
            write!(out, "V{idx}").unwrap();
        }
        Expr::Const(c) => {
            out.push_str("C:");
            out.push_str(const_name(c));
        }
        Expr::Lit(_, _) => out.push('L'),
        Expr::App(f, x) => {
            out.push_str("(@ ");
            walk(f, out, free_vars, bound_stack, next_bound);
            out.push(' ');
            walk(x, out, free_vars, bound_stack, next_bound);
            out.push(')');
        }
        Expr::Lam(bname, ty, body) => {
            out.push_str("(lam ");
            // type annotation lives in the OUTER scope (the binder isn't visible there)
            walk(ty, out, free_vars, bound_stack, next_bound);
            out.push(' ');
            // body is in a new scope where bname is bound to the next bound index
            let mut scope = HashMap::new();
            let idx = *next_bound;
            *next_bound += 1;
            scope.insert(bname.clone(), idx);
            bound_stack.push(scope);
            walk(body, out, free_vars, bound_stack, next_bound);
            bound_stack.pop();
            out.push(')');
        }
        Expr::Pi(bname, ty, body) => {
            out.push_str("(pi ");
            walk(ty, out, free_vars, bound_stack, next_bound);
            out.push(' ');
            let mut scope = HashMap::new();
            let idx = *next_bound;
            *next_bound += 1;
            scope.insert(bname.clone(), idx);
            bound_stack.push(scope);
            walk(body, out, free_vars, bound_stack, next_bound);
            bound_stack.pop();
            out.push(')');
        }
        Expr::BinOp(op, l, r) => {
            out.push('(');
            out.push_str(binop_name(op));
            out.push(' ');
            walk(l, out, free_vars, bound_stack, next_bound);
            out.push(' ');
            walk(r, out, free_vars, bound_stack, next_bound);
            out.push(')');
        }
        Expr::UnOp(op, e) => {
            out.push('(');
            out.push_str(unop_name(op));
            out.push(' ');
            walk(e, out, free_vars, bound_stack, next_bound);
            out.push(')');
        }
        Expr::Deriv(e, bvar) => {
            out.push_str("(deriv ");
            // The differentiation variable binds inside `e` — push a scope so
            // any Var(bvar) inside resolves to B<idx>.
            let mut scope = HashMap::new();
            let idx = *next_bound;
            *next_bound += 1;
            scope.insert(bvar.clone(), idx);
            bound_stack.push(scope);
            walk(e, out, free_vars, bound_stack, next_bound);
            bound_stack.pop();
            out.push(')');
        }
        Expr::PartialDeriv(e, bvar) => {
            out.push_str("(pderiv ");
            let mut scope = HashMap::new();
            let idx = *next_bound;
            *next_bound += 1;
            scope.insert(bvar.clone(), idx);
            bound_stack.push(scope);
            walk(e, out, free_vars, bound_stack, next_bound);
            bound_stack.pop();
            out.push(')');
        }
        Expr::Integral {
            body,
            lower,
            upper,
            var,
        } => {
            out.push_str("(int ");
            // body is in scope of var
            let mut scope = HashMap::new();
            let idx = *next_bound;
            *next_bound += 1;
            scope.insert(var.clone(), idx);
            bound_stack.push(scope);
            walk(body, out, free_vars, bound_stack, next_bound);
            bound_stack.pop();
            // lower / upper live in the OUTER scope; emit a sentinel for
            // absent bounds so (None, Some(u)) and (Some(u), None) diverge.
            out.push(' ');
            match lower {
                Some(l) => walk(l, out, free_vars, bound_stack, next_bound),
                None => out.push('_'),
            }
            out.push(' ');
            match upper {
                Some(u) => walk(u, out, free_vars, bound_stack, next_bound),
                None => out.push('_'),
            }
            out.push(')');
        }
        Expr::Sum {
            body,
            lower,
            upper,
            var,
        } => {
            out.push_str("(sum ");
            let mut scope = HashMap::new();
            let idx = *next_bound;
            *next_bound += 1;
            scope.insert(var.clone(), idx);
            bound_stack.push(scope);
            walk(body, out, free_vars, bound_stack, next_bound);
            bound_stack.pop();
            out.push(' ');
            walk(lower, out, free_vars, bound_stack, next_bound);
            out.push(' ');
            walk(upper, out, free_vars, bound_stack, next_bound);
            out.push(')');
        }
        Expr::Prod {
            body,
            lower,
            upper,
            var,
        } => {
            out.push_str("(prod ");
            let mut scope = HashMap::new();
            let idx = *next_bound;
            *next_bound += 1;
            scope.insert(var.clone(), idx);
            bound_stack.push(scope);
            walk(body, out, free_vars, bound_stack, next_bound);
            bound_stack.pop();
            out.push(' ');
            walk(lower, out, free_vars, bound_stack, next_bound);
            out.push(' ');
            walk(upper, out, free_vars, bound_stack, next_bound);
            out.push(')');
        }
        Expr::Limit {
            body,
            approaching,
            var,
        } => {
            out.push_str("(lim ");
            let mut scope = HashMap::new();
            let idx = *next_bound;
            *next_bound += 1;
            scope.insert(var.clone(), idx);
            bound_stack.push(scope);
            walk(body, out, free_vars, bound_stack, next_bound);
            bound_stack.pop();
            out.push(' ');
            // approaching is in the OUTER scope
            walk(approaching, out, free_vars, bound_stack, next_bound);
            out.push(')');
        }
        Expr::Let(bname, val, body) => {
            out.push_str("(let ");
            // val is in the OUTER scope (Rust let semantics, not letrec)
            walk(val, out, free_vars, bound_stack, next_bound);
            out.push(' ');
            let mut scope = HashMap::new();
            let idx = *next_bound;
            *next_bound += 1;
            scope.insert(bname.clone(), idx);
            bound_stack.push(scope);
            walk(body, out, free_vars, bound_stack, next_bound);
            bound_stack.pop();
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

    #[test]
    fn free_variable_leak_through_binder_diverges() {
        // (λx. x) + y     !=     (λx. y) + x
        use crate::expr::Expr;
        let body_id = Expr::Lam(
            "x".into(),
            Box::new(Expr::Var("T".into())),
            Box::new(Expr::Var("x".into())),
        );
        let body_const = Expr::Lam(
            "x".into(),
            Box::new(Expr::Var("T".into())),
            Box::new(Expr::Var("y".into())),
        );
        let e1 = Expr::BinOp(
            BinOp::Add,
            Box::new(body_id),
            Box::new(Expr::Var("y".into())),
        );
        let e2 = Expr::BinOp(
            BinOp::Add,
            Box::new(body_const),
            Box::new(Expr::Var("x".into())),
        );
        assert_ne!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn alpha_renamed_lambdas_collide() {
        // λx. x   ==   λy. y
        use crate::expr::Expr;
        let e1 = Expr::Lam(
            "x".into(),
            Box::new(Expr::Var("T".into())),
            Box::new(Expr::Var("x".into())),
        );
        let e2 = Expr::Lam(
            "y".into(),
            Box::new(Expr::Var("T".into())),
            Box::new(Expr::Var("y".into())),
        );
        assert_eq!(skeleton_hash(&e1), skeleton_hash(&e2));
    }

    #[test]
    fn integral_with_only_lower_diverges_from_only_upper() {
        use crate::expr::Expr;
        let f = Box::new(Expr::Var("f".into()));
        let bound = Box::new(Expr::Var("a".into()));
        let only_lower = Expr::Integral {
            body: f.clone(),
            var: "x".into(),
            lower: Some(bound.clone()),
            upper: None,
        };
        let only_upper = Expr::Integral {
            body: f,
            var: "x".into(),
            lower: None,
            upper: Some(bound),
        };
        assert_ne!(skeleton_hash(&only_lower), skeleton_hash(&only_upper));
    }

    #[test]
    fn deriv_and_pderiv_diverge() {
        use crate::expr::Expr;
        let e = Box::new(Expr::Var("f".into()));
        let d = Expr::Deriv(e.clone(), "x".into());
        let p = Expr::PartialDeriv(e, "x".into());
        assert_ne!(skeleton_hash(&d), skeleton_hash(&p));
    }

    #[test]
    fn sum_and_prod_diverge() {
        use crate::expr::Expr;
        let body = Box::new(Expr::Var("i".into()));
        let lo = Box::new(Expr::Lit(0, 1));
        let hi = Box::new(Expr::Lit(10, 1));
        let s = Expr::Sum {
            body: body.clone(),
            var: "i".into(),
            lower: lo.clone(),
            upper: hi.clone(),
        };
        let p = Expr::Prod {
            body,
            var: "i".into(),
            lower: lo,
            upper: hi,
        };
        assert_ne!(skeleton_hash(&s), skeleton_hash(&p));
    }
}
