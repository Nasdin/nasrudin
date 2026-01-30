//! Subtree crossover on `Expr` AST trees.
//!
//! Picks a random subtree position in each parent and swaps them
//! to produce two offspring.

use nasrudin_core::Expr;
use rand::Rng;

/// Perform subtree crossover on two expression trees.
///
/// Selects a random subtree position in each parent and swaps them,
/// producing two offspring expressions.
pub fn subtree_crossover(a: &Expr, b: &Expr, rng: &mut impl Rng) -> (Expr, Expr) {
    let positions_a = count_positions(a);
    let positions_b = count_positions(b);

    if positions_a <= 1 || positions_b <= 1 {
        // Too small to crossover meaningfully; return clones
        return (a.clone(), b.clone());
    }

    // Pick random crossover points (skip root = position 0 for variety)
    let pos_a = rng.random_range(1..positions_a);
    let pos_b = rng.random_range(1..positions_b);

    // Extract subtrees at those positions
    let subtree_a = extract_subtree(a, pos_a);
    let subtree_b = extract_subtree(b, pos_b);

    // Replace subtrees to create offspring
    let offspring_a = replace_subtree(a, pos_a, &subtree_b);
    let offspring_b = replace_subtree(b, pos_b, &subtree_a);

    (offspring_a, offspring_b)
}

/// Count total number of subtree positions in an expression.
fn count_positions(expr: &Expr) -> usize {
    match expr {
        Expr::Var(_) | Expr::Const(_) | Expr::Lit(_, _) => 1,
        Expr::App(f, x) => 1 + count_positions(f) + count_positions(x),
        Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) => {
            1 + count_positions(ty) + count_positions(body)
        }
        Expr::BinOp(_, l, r) => 1 + count_positions(l) + count_positions(r),
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => {
            1 + count_positions(e)
        }
        Expr::Integral {
            body,
            lower,
            upper,
            ..
        } => {
            1 + count_positions(body)
                + lower.as_ref().map_or(0, |e| count_positions(e))
                + upper.as_ref().map_or(0, |e| count_positions(e))
        }
        Expr::Sum {
            body,
            lower,
            upper,
            ..
        }
        | Expr::Prod {
            body,
            lower,
            upper,
            ..
        } => 1 + count_positions(body) + count_positions(lower) + count_positions(upper),
        Expr::Limit {
            body, approaching, ..
        } => 1 + count_positions(body) + count_positions(approaching),
        Expr::Let(_, val, body) => 1 + count_positions(val) + count_positions(body),
    }
}

/// Extract the subtree at a given DFS position index.
fn extract_subtree(expr: &Expr, target: usize) -> Expr {
    fn walk(expr: &Expr, pos: &mut usize, target: usize) -> Option<Expr> {
        if *pos == target {
            return Some(expr.clone());
        }
        *pos += 1;
        match expr {
            Expr::Var(_) | Expr::Const(_) | Expr::Lit(_, _) => None,
            Expr::App(f, x) => walk(f, pos, target).or_else(|| walk(x, pos, target)),
            Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) => {
                walk(ty, pos, target).or_else(|| walk(body, pos, target))
            }
            Expr::BinOp(_, l, r) => walk(l, pos, target).or_else(|| walk(r, pos, target)),
            Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => {
                walk(e, pos, target)
            }
            Expr::Integral {
                body,
                lower,
                upper,
                ..
            } => walk(body, pos, target)
                .or_else(|| lower.as_ref().and_then(|e| walk(e, pos, target)))
                .or_else(|| upper.as_ref().and_then(|e| walk(e, pos, target))),
            Expr::Sum {
                body,
                lower,
                upper,
                ..
            }
            | Expr::Prod {
                body,
                lower,
                upper,
                ..
            } => walk(body, pos, target)
                .or_else(|| walk(lower, pos, target))
                .or_else(|| walk(upper, pos, target)),
            Expr::Limit {
                body, approaching, ..
            } => walk(body, pos, target).or_else(|| walk(approaching, pos, target)),
            Expr::Let(_, val, body) => {
                walk(val, pos, target).or_else(|| walk(body, pos, target))
            }
        }
    }

    let mut pos = 0;
    walk(expr, &mut pos, target).unwrap_or_else(|| expr.clone())
}

/// Replace the subtree at a given DFS position index with `replacement`.
fn replace_subtree(expr: &Expr, target: usize, replacement: &Expr) -> Expr {
    fn walk(expr: &Expr, pos: &mut usize, target: usize, replacement: &Expr) -> Expr {
        if *pos == target {
            *pos += count_skip(expr); // skip children
            return replacement.clone();
        }
        *pos += 1;
        match expr {
            Expr::Var(_) | Expr::Const(_) | Expr::Lit(_, _) => expr.clone(),
            Expr::App(f, x) => {
                let f2 = walk(f, pos, target, replacement);
                let x2 = walk(x, pos, target, replacement);
                Expr::App(Box::new(f2), Box::new(x2))
            }
            Expr::Lam(s, ty, body) => {
                let ty2 = walk(ty, pos, target, replacement);
                let body2 = walk(body, pos, target, replacement);
                Expr::Lam(s.clone(), Box::new(ty2), Box::new(body2))
            }
            Expr::Pi(s, ty, body) => {
                let ty2 = walk(ty, pos, target, replacement);
                let body2 = walk(body, pos, target, replacement);
                Expr::Pi(s.clone(), Box::new(ty2), Box::new(body2))
            }
            Expr::BinOp(op, l, r) => {
                let l2 = walk(l, pos, target, replacement);
                let r2 = walk(r, pos, target, replacement);
                Expr::BinOp(op.clone(), Box::new(l2), Box::new(r2))
            }
            Expr::UnOp(op, e) => {
                let e2 = walk(e, pos, target, replacement);
                Expr::UnOp(op.clone(), Box::new(e2))
            }
            Expr::Deriv(e, s) => {
                let e2 = walk(e, pos, target, replacement);
                Expr::Deriv(Box::new(e2), s.clone())
            }
            Expr::PartialDeriv(e, s) => {
                let e2 = walk(e, pos, target, replacement);
                Expr::PartialDeriv(Box::new(e2), s.clone())
            }
            Expr::Integral {
                body,
                var,
                lower,
                upper,
            } => {
                let body2 = walk(body, pos, target, replacement);
                let lower2 = lower
                    .as_ref()
                    .map(|e| Box::new(walk(e, pos, target, replacement)));
                let upper2 = upper
                    .as_ref()
                    .map(|e| Box::new(walk(e, pos, target, replacement)));
                Expr::Integral {
                    body: Box::new(body2),
                    var: var.clone(),
                    lower: lower2,
                    upper: upper2,
                }
            }
            Expr::Sum {
                body,
                var,
                lower,
                upper,
            } => {
                let body2 = walk(body, pos, target, replacement);
                let lower2 = walk(lower, pos, target, replacement);
                let upper2 = walk(upper, pos, target, replacement);
                Expr::Sum {
                    body: Box::new(body2),
                    var: var.clone(),
                    lower: Box::new(lower2),
                    upper: Box::new(upper2),
                }
            }
            Expr::Prod {
                body,
                var,
                lower,
                upper,
            } => {
                let body2 = walk(body, pos, target, replacement);
                let lower2 = walk(lower, pos, target, replacement);
                let upper2 = walk(upper, pos, target, replacement);
                Expr::Prod {
                    body: Box::new(body2),
                    var: var.clone(),
                    lower: Box::new(lower2),
                    upper: Box::new(upper2),
                }
            }
            Expr::Limit {
                body,
                var,
                approaching,
            } => {
                let body2 = walk(body, pos, target, replacement);
                let approaching2 = walk(approaching, pos, target, replacement);
                Expr::Limit {
                    body: Box::new(body2),
                    var: var.clone(),
                    approaching: Box::new(approaching2),
                }
            }
            Expr::Let(s, val, body) => {
                let val2 = walk(val, pos, target, replacement);
                let body2 = walk(body, pos, target, replacement);
                Expr::Let(s.clone(), Box::new(val2), Box::new(body2))
            }
        }
    }

    let mut pos = 0;
    walk(expr, &mut pos, target, replacement)
}

/// Count the total nodes in an expression (used to skip during replacement).
fn count_skip(expr: &Expr) -> usize {
    count_positions(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_core::BinOp;

    #[test]
    fn crossover_preserves_structure() {
        // E = m * c^2
        let e_eq = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("E".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Var("m".into())),
                Box::new(Expr::BinOp(
                    BinOp::Pow,
                    Box::new(Expr::Var("c".into())),
                    Box::new(Expr::Lit(2, 1)),
                )),
            )),
        );

        // F = m * a
        let f_eq = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("F".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Var("m".into())),
                Box::new(Expr::Var("a".into())),
            )),
        );

        let mut rng = rand::rng();
        let (child_a, child_b) = subtree_crossover(&e_eq, &f_eq, &mut rng);

        // Both children should have at least 1 node
        assert!(child_a.node_count() >= 1);
        assert!(child_b.node_count() >= 1);
    }

    #[test]
    fn count_positions_simple() {
        let expr = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Lit(1, 1)),
        );
        assert_eq!(count_positions(&expr), 3);
    }
}
