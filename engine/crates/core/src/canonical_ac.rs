//! AC-canonical normalization of `Expr`.
//!
//! Two formulas that differ only by:
//!   * commuting operands of `+`, `*`, `and`, `or`,
//!   * associating those operands differently,
//!   * subtraction vs `a + (-b)`,
//!   * division vs `a * b^(-1)`,
//!   * unreduced rational literals,
//!   * double negation, or
//!   * the sides of an equation (`a = b` vs `b = a`),
//!
//! collapse to the same `Expr` and therefore the same hash. Used by the
//! search layer to answer "does the corpus already contain my conjecture?"
//! independent of how it was written.
//!
//! Not normalized in v1: distributivity, identity-element folding
//! (`x + 0`, `x * 1`), or alpha-renaming of bound variables. Callers can
//! pre-apply `derive::rewrite::simplify` for those.

use crate::expr::{BinOp, Expr, UnOp};
use xxhash_rust::xxh64::xxh64;

/// Returns an AC-normalized clone of `e`.
pub fn to_canonical_ac(e: &Expr) -> Expr {
    normalize(e)
}

/// `to_canonical()` of the AC-normalized form. Stable string identity for
/// AC-equivalent expressions.
pub fn canonical_ac_string(e: &Expr) -> String {
    to_canonical_ac(e).to_canonical()
}

/// 8-byte xxHash64 of [`canonical_ac_string`]. Suitable for a PG `binary(8)`
/// column.
pub fn canonical_ac_hash(e: &Expr) -> [u8; 8] {
    xxh64(canonical_ac_string(e).as_bytes(), 0).to_le_bytes()
}

fn normalize(e: &Expr) -> Expr {
    match e {
        Expr::Var(_) | Expr::Const(_) => e.clone(),
        Expr::Lit(n, d) => normalize_lit(*n, *d),
        Expr::App(f, x) => Expr::App(b(normalize(f)), b(normalize(x))),

        Expr::UnOp(UnOp::Neg, inner) => normalize_neg(inner),
        Expr::UnOp(op, inner) => Expr::UnOp(op.clone(), b(normalize(inner))),

        Expr::BinOp(BinOp::Sub, l, r) => {
            // a - b -> a + (-b), then re-normalize so the resulting Add
            // participates in AC sorting.
            normalize(&Expr::BinOp(
                BinOp::Add,
                l.clone(),
                Box::new(Expr::UnOp(UnOp::Neg, r.clone())),
            ))
        }
        Expr::BinOp(BinOp::Div, l, r) => {
            // a / b -> a * b^(-1)
            normalize(&Expr::BinOp(
                BinOp::Mul,
                l.clone(),
                Box::new(Expr::BinOp(
                    BinOp::Pow,
                    r.clone(),
                    Box::new(Expr::Lit(-1, 1)),
                )),
            ))
        }
        Expr::BinOp(op, _, _) if is_ac_op(op) => {
            let mut leaves = Vec::new();
            collect_ac(op, e, &mut leaves);
            let mut normalized: Vec<Expr> = leaves.iter().map(normalize).collect();
            normalized.sort_by(|a, b| a.to_canonical().cmp(&b.to_canonical()));
            rebuild_ac(op, normalized)
        }
        Expr::BinOp(op, l, r) if is_symmetric_relation(op) => {
            let nl = normalize(l);
            let nr = normalize(r);
            if nl.to_canonical() <= nr.to_canonical() {
                Expr::BinOp(op.clone(), b(nl), b(nr))
            } else {
                Expr::BinOp(op.clone(), b(nr), b(nl))
            }
        }
        Expr::BinOp(op, l, r) => {
            Expr::BinOp(op.clone(), b(normalize(l)), b(normalize(r)))
        }

        Expr::Deriv(inner, v) => Expr::Deriv(b(normalize(inner)), v.clone()),
        Expr::PartialDeriv(inner, v) => Expr::PartialDeriv(b(normalize(inner)), v.clone()),
        Expr::Integral {
            body,
            var,
            lower,
            upper,
        } => Expr::Integral {
            body: b(normalize(body)),
            var: var.clone(),
            lower: lower.as_ref().map(|e| b(normalize(e))),
            upper: upper.as_ref().map(|e| b(normalize(e))),
        },
        Expr::Sum {
            body,
            var,
            lower,
            upper,
        } => Expr::Sum {
            body: b(normalize(body)),
            var: var.clone(),
            lower: b(normalize(lower)),
            upper: b(normalize(upper)),
        },
        Expr::Prod {
            body,
            var,
            lower,
            upper,
        } => Expr::Prod {
            body: b(normalize(body)),
            var: var.clone(),
            lower: b(normalize(lower)),
            upper: b(normalize(upper)),
        },
        Expr::Limit {
            body,
            var,
            approaching,
        } => Expr::Limit {
            body: b(normalize(body)),
            var: var.clone(),
            approaching: b(normalize(approaching)),
        },
        Expr::Lam(v, ty, body) => Expr::Lam(v.clone(), b(normalize(ty)), b(normalize(body))),
        Expr::Pi(v, ty, body) => Expr::Pi(v.clone(), b(normalize(ty)), b(normalize(body))),
        Expr::Let(v, val, body) => Expr::Let(v.clone(), b(normalize(val)), b(normalize(body))),
    }
}

fn b(e: Expr) -> Box<Expr> {
    Box::new(e)
}

fn is_ac_op(op: &BinOp) -> bool {
    matches!(op, BinOp::Add | BinOp::Mul | BinOp::And | BinOp::Or)
}

fn is_symmetric_relation(op: &BinOp) -> bool {
    matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Iff)
}

fn collect_ac(op: &BinOp, e: &Expr, out: &mut Vec<Expr>) {
    if let Expr::BinOp(eop, l, r) = e {
        if eop == op {
            collect_ac(op, l, out);
            collect_ac(op, r, out);
            return;
        }
    }
    out.push(e.clone());
}

fn rebuild_ac(op: &BinOp, mut nodes: Vec<Expr>) -> Expr {
    debug_assert!(!nodes.is_empty(), "AC operator with no operands");
    if nodes.len() == 1 {
        return nodes.pop().unwrap();
    }
    // Right-leaning rebuild: x0 op (x1 op (x2 op ... xn))
    let last = nodes.pop().unwrap();
    nodes
        .into_iter()
        .rev()
        .fold(last, |acc, x| Expr::BinOp(op.clone(), Box::new(x), Box::new(acc)))
}

fn normalize_lit(n: i64, d: u64) -> Expr {
    // Defensive: a zero denominator is invalid input; treat as integer.
    if d == 0 {
        return Expr::Lit(n, 1);
    }
    if n == 0 {
        return Expr::Lit(0, 1);
    }
    let g = gcd(n.unsigned_abs(), d);
    Expr::Lit(n / g as i64, d / g)
}

fn normalize_neg(inner: &Expr) -> Expr {
    let n = normalize(inner);
    match n {
        Expr::UnOp(UnOp::Neg, x) => *x,            // --x -> x
        Expr::Lit(num, den) => Expr::Lit(-num, den), // -literal pushes sign onto numerator
        other => Expr::UnOp(UnOp::Neg, Box::new(other)),
    }
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a.max(1)
    } else {
        gcd(b, a % b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(name: &str) -> Expr {
        Expr::Var(name.into())
    }

    fn add(a: Expr, b: Expr) -> Expr {
        Expr::BinOp(BinOp::Add, Box::new(a), Box::new(b))
    }

    fn mul(a: Expr, b: Expr) -> Expr {
        Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(b))
    }

    fn sub(a: Expr, b: Expr) -> Expr {
        Expr::BinOp(BinOp::Sub, Box::new(a), Box::new(b))
    }

    fn div(a: Expr, b: Expr) -> Expr {
        Expr::BinOp(BinOp::Div, Box::new(a), Box::new(b))
    }

    fn pow(a: Expr, b: Expr) -> Expr {
        Expr::BinOp(BinOp::Pow, Box::new(a), Box::new(b))
    }

    fn eq(a: Expr, b: Expr) -> Expr {
        Expr::BinOp(BinOp::Eq, Box::new(a), Box::new(b))
    }

    fn neg(e: Expr) -> Expr {
        Expr::UnOp(UnOp::Neg, Box::new(e))
    }

    #[test]
    fn add_is_commutative() {
        assert_eq!(canonical_ac_hash(&add(v("a"), v("b"))), canonical_ac_hash(&add(v("b"), v("a"))));
    }

    #[test]
    fn mul_is_commutative() {
        assert_eq!(canonical_ac_hash(&mul(v("a"), v("b"))), canonical_ac_hash(&mul(v("b"), v("a"))));
    }

    #[test]
    fn add_is_associative() {
        // (a + b) + c == a + (b + c)
        let l = add(add(v("a"), v("b")), v("c"));
        let r = add(v("a"), add(v("b"), v("c")));
        assert_eq!(canonical_ac_hash(&l), canonical_ac_hash(&r));
    }

    #[test]
    fn add_n_ary_full_permutation() {
        // c + a + b == a + b + c (any associativity / order)
        let l = add(v("c"), add(v("a"), v("b")));
        let r = add(add(v("a"), v("b")), v("c"));
        assert_eq!(canonical_ac_hash(&l), canonical_ac_hash(&r));
        // Sorted order: a then b then c
        assert_eq!(canonical_ac_string(&l), "(+ v:a (+ v:b v:c))");
    }

    #[test]
    fn distributivity_is_not_applied() {
        // a*(b+c) and (a*b)+(a*c) must NOT match — v1 is AC-only.
        let dist = mul(v("a"), add(v("b"), v("c")));
        let expanded = add(mul(v("a"), v("b")), mul(v("a"), v("c")));
        assert_ne!(canonical_ac_hash(&dist), canonical_ac_hash(&expanded));
    }

    #[test]
    fn sub_normalizes_into_add_neg() {
        // a - b -> a + (-b), then sorted by canonical of children
        let s = sub(v("a"), v("b"));
        let expected = add(v("a"), neg(v("b")));
        assert_eq!(canonical_ac_hash(&s), canonical_ac_hash(&expected));
    }

    #[test]
    fn double_subtraction_collapses() {
        // a - (-b) -> a + b
        let s = sub(v("a"), neg(v("b")));
        let plus = add(v("a"), v("b"));
        assert_eq!(canonical_ac_hash(&s), canonical_ac_hash(&plus));
    }

    #[test]
    fn div_normalizes_into_mul_pow_neg_one() {
        let d = div(v("a"), v("b"));
        let expected = mul(v("a"), pow(v("b"), Expr::Lit(-1, 1)));
        assert_eq!(canonical_ac_hash(&d), canonical_ac_hash(&expected));
    }

    #[test]
    fn lit_reduces_to_lowest_terms() {
        let big = Expr::Lit(6, 9);
        let small = Expr::Lit(2, 3);
        assert_eq!(canonical_ac_hash(&big), canonical_ac_hash(&small));
    }

    #[test]
    fn lit_zero_collapses_denominator() {
        let zero = Expr::Lit(0, 7);
        let canon = Expr::Lit(0, 1);
        assert_eq!(canonical_ac_hash(&zero), canonical_ac_hash(&canon));
    }

    #[test]
    fn double_neg_collapses() {
        let dn = neg(neg(v("x")));
        assert_eq!(canonical_ac_hash(&dn), canonical_ac_hash(&v("x")));
    }

    #[test]
    fn neg_lit_pushes_sign_into_numerator() {
        let nl = neg(Expr::Lit(3, 1));
        let direct = Expr::Lit(-3, 1);
        assert_eq!(canonical_ac_hash(&nl), canonical_ac_hash(&direct));
    }

    #[test]
    fn equality_is_symmetric() {
        let lhs = eq(v("a"), v("b"));
        let rhs = eq(v("b"), v("a"));
        assert_eq!(canonical_ac_hash(&lhs), canonical_ac_hash(&rhs));
    }

    #[test]
    fn implication_is_not_symmetric() {
        // Implies is asymmetric — must NOT collapse.
        let ab = Expr::BinOp(BinOp::Implies, Box::new(v("a")), Box::new(v("b")));
        let ba = Expr::BinOp(BinOp::Implies, Box::new(v("b")), Box::new(v("a")));
        assert_ne!(canonical_ac_hash(&ab), canonical_ac_hash(&ba));
    }

    #[test]
    fn pow_is_not_commutative() {
        let ab = pow(v("a"), v("b"));
        let ba = pow(v("b"), v("a"));
        assert_ne!(canonical_ac_hash(&ab), canonical_ac_hash(&ba));
    }

    #[test]
    fn idempotent() {
        // Normalizing an already-normal form must be a fixed point.
        let e = add(v("c"), add(v("a"), v("b")));
        let once = to_canonical_ac(&e);
        let twice = to_canonical_ac(&once);
        assert_eq!(once, twice);
    }

    #[test]
    fn commutator_emc2_squared_form() {
        // [E^2 = (pc)^2 + (mc^2)^2]  vs reordered RHS.
        let lhs = pow(v("E"), Expr::Lit(2, 1));
        let pc2 = pow(mul(v("p"), v("c")), Expr::Lit(2, 1));
        let mc22 = pow(mul(v("m"), pow(v("c"), Expr::Lit(2, 1))), Expr::Lit(2, 1));
        let a = eq(lhs.clone(), add(pc2.clone(), mc22.clone()));
        let b = eq(add(mc22, pc2), lhs);
        assert_eq!(canonical_ac_hash(&a), canonical_ac_hash(&b));
    }

    #[test]
    fn nested_recursion_inside_non_ac_context() {
        // Pow is non-AC, but its operands must still be AC-normalized.
        let inside_a = pow(add(v("x"), v("y")), v("n"));
        let inside_b = pow(add(v("y"), v("x")), v("n"));
        assert_eq!(canonical_ac_hash(&inside_a), canonical_ac_hash(&inside_b));
    }
}
