use nasrudin_core::{BinOp, Expr, PhysConst};
use nasrudin_derive::rewrite::{apply_substitution, match_expr, simplify, substitute_in_equation};
use std::collections::HashMap;

fn var(name: &str) -> Expr {
    Expr::Var(name.into())
}

fn lit(n: i64) -> Expr {
    Expr::Lit(n, 1)
}

fn add(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp::Add, Box::new(l), Box::new(r))
}

fn mul(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp::Mul, Box::new(l), Box::new(r))
}

fn pow(base: Expr, exp: Expr) -> Expr {
    Expr::BinOp(BinOp::Pow, Box::new(base), Box::new(exp))
}

fn eq(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp::Eq, Box::new(l), Box::new(r))
}

fn sub(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp::Sub, Box::new(l), Box::new(r))
}

#[test]
fn test_match_expr_variable_binding() {
    // Pattern: x + y, Expr: a + b
    let pattern = add(var("x"), var("y"));
    let expr = add(var("a"), var("b"));
    let result = match_expr(&pattern, &expr);
    assert!(result.is_some());
    let bindings = result.unwrap();
    assert_eq!(bindings.get("x"), Some(&var("a")));
    assert_eq!(bindings.get("y"), Some(&var("b")));
}

#[test]
fn test_match_expr_consistent_binding() {
    // Pattern: x + x (same var twice), Expr: a + a → match
    let pattern = add(var("x"), var("x"));
    let expr = add(var("a"), var("a"));
    assert!(match_expr(&pattern, &expr).is_some());

    // Pattern: x + x, Expr: a + b → no match (inconsistent)
    let expr2 = add(var("a"), var("b"));
    assert!(match_expr(&pattern, &expr2).is_none());
}

#[test]
fn test_match_expr_literal() {
    let pattern = lit(42);
    assert!(match_expr(&pattern, &lit(42)).is_some());
    assert!(match_expr(&pattern, &lit(43)).is_none());
}

#[test]
fn test_match_expr_constant() {
    let pattern = Expr::Const(PhysConst::SpeedOfLight);
    assert!(match_expr(&pattern, &Expr::Const(PhysConst::SpeedOfLight)).is_some());
    assert!(match_expr(&pattern, &Expr::Const(PhysConst::PlanckConst)).is_none());
}

#[test]
fn test_apply_substitution_simple() {
    let expr = add(var("x"), var("y"));
    let mut subst = HashMap::new();
    subst.insert("x".into(), lit(3));
    subst.insert("y".into(), lit(4));
    let result = apply_substitution(&expr, &subst);
    assert_eq!(result, add(lit(3), lit(4)));
}

#[test]
fn test_apply_substitution_nested() {
    // x * (y + z) with x→2
    let expr = mul(var("x"), add(var("y"), var("z")));
    let mut subst = HashMap::new();
    subst.insert("x".into(), lit(2));
    let result = apply_substitution(&expr, &subst);
    assert_eq!(result, mul(lit(2), add(var("y"), var("z"))));
}

#[test]
fn test_simplify_zero_add() {
    // 0 + x → x
    assert_eq!(simplify(&add(lit(0), var("x"))), var("x"));
    // x + 0 → x
    assert_eq!(simplify(&add(var("x"), lit(0))), var("x"));
}

#[test]
fn test_simplify_zero_mul() {
    // 0 * x → 0
    assert_eq!(simplify(&mul(lit(0), var("x"))), lit(0));
    // x * 0 → 0
    assert_eq!(simplify(&mul(var("x"), lit(0))), lit(0));
}

#[test]
fn test_simplify_one_mul() {
    // 1 * x → x
    assert_eq!(simplify(&mul(lit(1), var("x"))), var("x"));
    // x * 1 → x
    assert_eq!(simplify(&mul(var("x"), lit(1))), var("x"));
}

#[test]
fn test_simplify_pow_zero() {
    // x^0 → 1
    assert_eq!(simplify(&pow(var("x"), lit(0))), lit(1));
}

#[test]
fn test_simplify_pow_one() {
    // x^1 → x
    assert_eq!(simplify(&pow(var("x"), lit(1))), var("x"));
}

#[test]
fn test_simplify_zero_pow() {
    // 0^2 → 0
    assert_eq!(simplify(&pow(lit(0), lit(2))), lit(0));
}

#[test]
fn test_simplify_literal_arithmetic() {
    // 3 + 4 → 7
    assert_eq!(simplify(&add(lit(3), lit(4))), lit(7));
    // 3 * 4 → 12
    assert_eq!(simplify(&mul(lit(3), lit(4))), Expr::Lit(12, 1));
}

#[test]
fn test_simplify_nested() {
    // 0^2 * c^2 + (m * c^2)^2
    // After simplification: 0 * c^2 + (m * c^2)^2 → 0 + (m * c^2)^2 → (m * c^2)^2
    let c = Expr::Const(PhysConst::SpeedOfLight);
    let zero_sq = pow(lit(0), lit(2));
    let c_sq = pow(c.clone(), lit(2));
    let term1 = mul(zero_sq, c_sq.clone());
    let mc_sq = mul(var("m"), c_sq);
    let term2 = pow(mc_sq.clone(), lit(2));
    let expr = add(term1, term2.clone());

    let result = simplify(&expr);
    assert_eq!(result, term2);
}

#[test]
fn test_substitute_p_zero_in_equation() {
    // E² = p²c² + (mc²)²  with p=0
    let e_sq = pow(var("E"), lit(2));
    let p_sq = pow(var("p"), lit(2));
    let c = Expr::Const(PhysConst::SpeedOfLight);
    let c_sq = pow(c.clone(), lit(2));
    let p_sq_c_sq = mul(p_sq, c_sq.clone());
    let mc_sq = mul(var("m"), c_sq);
    let mc_sq_sq = pow(mc_sq, lit(2));
    let rhs = add(p_sq_c_sq, mc_sq_sq);
    let equation = eq(e_sq.clone(), rhs);

    let result = substitute_in_equation(&equation, "p", &lit(0));

    // After substitution, p should be replaced with 0
    // E² = 0²c² + (mc²)²
    if let Expr::BinOp(BinOp::Eq, lhs, rhs) = &result {
        assert_eq!(**lhs, e_sq);
        // RHS should contain 0 where p was
        let canonical = rhs.to_canonical();
        assert!(canonical.contains("n:0"), "RHS should contain 0: {canonical}");
    } else {
        panic!("Expected equation");
    }
}

#[test]
fn test_sub_equal_terms() {
    // x - x → 0
    assert_eq!(simplify(&sub(var("x"), var("x"))), lit(0));
}
