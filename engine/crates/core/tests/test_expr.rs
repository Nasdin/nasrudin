use physics_core::expr::*;

#[test]
fn test_var_node_count() {
    let e = Expr::Var("x".to_string());
    assert_eq!(e.node_count(), 1);
}

#[test]
fn test_const_node_count() {
    let e = Expr::Const(PhysConst::SpeedOfLight);
    assert_eq!(e.node_count(), 1);
}

#[test]
fn test_lit_node_count() {
    let e = Expr::Lit(42, 1);
    assert_eq!(e.node_count(), 1);
}

#[test]
fn test_binop_node_count() {
    // x + y => 3 nodes (Add, x, y)
    let e = Expr::BinOp(
        BinOp::Add,
        Box::new(Expr::Var("x".into())),
        Box::new(Expr::Var("y".into())),
    );
    assert_eq!(e.node_count(), 3);
}

#[test]
fn test_unop_node_count() {
    // sin(x) => 2 nodes
    let e = Expr::UnOp(UnOp::Sin, Box::new(Expr::Var("x".into())));
    assert_eq!(e.node_count(), 2);
}

#[test]
fn test_emc2_node_count() {
    // E = m * c^2
    // Eq(Var(E), Mul(Var(m), Pow(Const(c), Lit(2,1))))
    // Nodes: Eq(1) + Var(E)(1) + Mul(1) + Var(m)(1) + Pow(1) + Const(c)(1) + Lit(2)(1) = 7
    let e = Expr::BinOp(
        BinOp::Eq,
        Box::new(Expr::Var("E".into())),
        Box::new(Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("m".into())),
            Box::new(Expr::BinOp(
                BinOp::Pow,
                Box::new(Expr::Const(PhysConst::SpeedOfLight)),
                Box::new(Expr::Lit(2, 1)),
            )),
        )),
    );
    assert_eq!(e.node_count(), 7);
}

#[test]
fn test_integral_node_count_with_bounds() {
    // integral_0^1 x dx => 1 (integral) + 1 (body:x) + 1 (lower:0) + 1 (upper:1) = 4
    let e = Expr::Integral {
        body: Box::new(Expr::Var("x".into())),
        var: "x".into(),
        lower: Some(Box::new(Expr::Lit(0, 1))),
        upper: Some(Box::new(Expr::Lit(1, 1))),
    };
    assert_eq!(e.node_count(), 4);
}

#[test]
fn test_integral_node_count_indefinite() {
    // integral x dx (no bounds) => 1 (integral) + 1 (body:x) = 2
    let e = Expr::Integral {
        body: Box::new(Expr::Var("x".into())),
        var: "x".into(),
        lower: None,
        upper: None,
    };
    assert_eq!(e.node_count(), 2);
}

#[test]
fn test_sum_node_count() {
    // sum_{i=0}^{n} i => 1 (sum) + 1 (body:i) + 1 (lower:0) + 1 (upper:n) = 4
    let e = Expr::Sum {
        body: Box::new(Expr::Var("i".into())),
        var: "i".into(),
        lower: Box::new(Expr::Lit(0, 1)),
        upper: Box::new(Expr::Var("n".into())),
    };
    assert_eq!(e.node_count(), 4);
}

#[test]
fn test_limit_node_count() {
    // lim_{x->0} x => 1 + 1 + 1 = 3
    let e = Expr::Limit {
        body: Box::new(Expr::Var("x".into())),
        var: "x".into(),
        approaching: Box::new(Expr::Lit(0, 1)),
    };
    assert_eq!(e.node_count(), 3);
}

#[test]
fn test_let_node_count() {
    // let x = 5 in x => 1 + 1 + 1 = 3
    let e = Expr::Let(
        "x".into(),
        Box::new(Expr::Lit(5, 1)),
        Box::new(Expr::Var("x".into())),
    );
    assert_eq!(e.node_count(), 3);
}

#[test]
fn test_deriv_node_count() {
    // d/dx (x) => 1 + 1 = 2
    let e = Expr::Deriv(Box::new(Expr::Var("x".into())), "x".into());
    assert_eq!(e.node_count(), 2);
}

#[test]
fn test_app_node_count() {
    // f(x) => 1 + 1 + 1 = 3
    let e = Expr::App(
        Box::new(Expr::Var("f".into())),
        Box::new(Expr::Var("x".into())),
    );
    assert_eq!(e.node_count(), 3);
}

// ---- Canonical form tests ----

#[test]
fn test_var_canonical() {
    let e = Expr::Var("x".into());
    assert_eq!(e.to_canonical(), "v:x");
}

#[test]
fn test_const_canonical() {
    let e = Expr::Const(PhysConst::SpeedOfLight);
    assert_eq!(e.to_canonical(), "c:SpeedOfLight");
}

#[test]
fn test_lit_integer_canonical() {
    let e = Expr::Lit(42, 1);
    assert_eq!(e.to_canonical(), "n:42");
}

#[test]
fn test_lit_rational_canonical() {
    let e = Expr::Lit(1, 2);
    assert_eq!(e.to_canonical(), "n:1/2");
}

#[test]
fn test_binop_add_canonical() {
    let e = Expr::BinOp(
        BinOp::Add,
        Box::new(Expr::Var("x".into())),
        Box::new(Expr::Var("y".into())),
    );
    assert_eq!(e.to_canonical(), "(+ v:x v:y)");
}

#[test]
fn test_emc2_canonical() {
    let e = Expr::BinOp(
        BinOp::Eq,
        Box::new(Expr::Var("E".into())),
        Box::new(Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("m".into())),
            Box::new(Expr::BinOp(
                BinOp::Pow,
                Box::new(Expr::Const(PhysConst::SpeedOfLight)),
                Box::new(Expr::Lit(2, 1)),
            )),
        )),
    );
    assert_eq!(e.to_canonical(), "(= v:E (* v:m (^ c:SpeedOfLight n:2)))");
}

#[test]
fn test_unop_canonical() {
    let e = Expr::UnOp(UnOp::Sin, Box::new(Expr::Var("x".into())));
    assert_eq!(e.to_canonical(), "(sin v:x)");
}

#[test]
fn test_deriv_canonical() {
    let e = Expr::Deriv(Box::new(Expr::Var("f".into())), "x".into());
    assert_eq!(e.to_canonical(), "(deriv x v:f)");
}

#[test]
fn test_integral_canonical() {
    let e = Expr::Integral {
        body: Box::new(Expr::Var("x".into())),
        var: "x".into(),
        lower: Some(Box::new(Expr::Lit(0, 1))),
        upper: Some(Box::new(Expr::Lit(1, 1))),
    };
    assert_eq!(e.to_canonical(), "(integral x n:0 n:1 v:x)");
}

#[test]
fn test_integral_indefinite_canonical() {
    let e = Expr::Integral {
        body: Box::new(Expr::Var("x".into())),
        var: "x".into(),
        lower: None,
        upper: None,
    };
    assert_eq!(e.to_canonical(), "(integral x _ _ v:x)");
}

#[test]
fn test_lambda_canonical() {
    let e = Expr::Lam(
        "x".into(),
        Box::new(Expr::Var("Real".into())),
        Box::new(Expr::Var("x".into())),
    );
    assert_eq!(e.to_canonical(), "(lambda x v:Real v:x)");
}

#[test]
fn test_pi_type_canonical() {
    let e = Expr::Pi(
        "x".into(),
        Box::new(Expr::Var("Nat".into())),
        Box::new(Expr::Var("Nat".into())),
    );
    assert_eq!(e.to_canonical(), "(pi x v:Nat v:Nat)");
}

#[test]
fn test_let_canonical() {
    let e = Expr::Let(
        "x".into(),
        Box::new(Expr::Lit(5, 1)),
        Box::new(Expr::Var("x".into())),
    );
    assert_eq!(e.to_canonical(), "(let x n:5 v:x)");
}

#[test]
fn test_sum_canonical() {
    let e = Expr::Sum {
        body: Box::new(Expr::Var("i".into())),
        var: "i".into(),
        lower: Box::new(Expr::Lit(1, 1)),
        upper: Box::new(Expr::Var("n".into())),
    };
    assert_eq!(e.to_canonical(), "(sum i n:1 v:n v:i)");
}

#[test]
fn test_limit_canonical() {
    let e = Expr::Limit {
        body: Box::new(Expr::Var("x".into())),
        var: "x".into(),
        approaching: Box::new(Expr::Lit(0, 1)),
    };
    assert_eq!(e.to_canonical(), "(limit x n:0 v:x)");
}

// ---- Serde round-trip tests ----

#[test]
fn test_expr_serde_roundtrip_simple() {
    let original = Expr::BinOp(
        BinOp::Add,
        Box::new(Expr::Var("x".into())),
        Box::new(Expr::Lit(1, 1)),
    );
    let json = serde_json::to_string(&original).unwrap();
    let restored: Expr = serde_json::from_str(&json).unwrap();
    assert_eq!(original, restored);
}

#[test]
fn test_expr_serde_roundtrip_complex() {
    let original = Expr::Integral {
        body: Box::new(Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::UnOp(UnOp::Sin, Box::new(Expr::Var("x".into())))),
        )),
        var: "x".into(),
        lower: Some(Box::new(Expr::Lit(0, 1))),
        upper: Some(Box::new(Expr::Const(PhysConst::Pi))),
    };
    let json = serde_json::to_string(&original).unwrap();
    let restored: Expr = serde_json::from_str(&json).unwrap();
    assert_eq!(original, restored);
}

// ---- All BinOp canonical strings ----

#[test]
fn test_all_binop_canonicals() {
    let check = |op: BinOp, expected: &str| {
        let e = Expr::BinOp(
            op,
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        assert_eq!(e.to_canonical(), format!("({expected} v:a v:b)"));
    };
    check(BinOp::Add, "+");
    check(BinOp::Sub, "-");
    check(BinOp::Mul, "*");
    check(BinOp::Div, "/");
    check(BinOp::Pow, "^");
    check(BinOp::Eq, "=");
    check(BinOp::Ne, "!=");
    check(BinOp::Lt, "<");
    check(BinOp::Le, "<=");
    check(BinOp::Gt, ">");
    check(BinOp::Ge, ">=");
    check(BinOp::And, "and");
    check(BinOp::Or, "or");
    check(BinOp::Implies, "->");
    check(BinOp::Iff, "<->");
    check(BinOp::Cross, "cross");
    check(BinOp::Dot, "dot");
    check(BinOp::TensorProduct, "tensor");
}

// ---- All UnOp canonical strings ----

#[test]
fn test_all_unop_canonicals() {
    let check = |op: UnOp, expected: &str| {
        let e = Expr::UnOp(op, Box::new(Expr::Var("x".into())));
        assert_eq!(e.to_canonical(), format!("({expected} v:x)"));
    };
    check(UnOp::Neg, "neg");
    check(UnOp::Abs, "abs");
    check(UnOp::Sqrt, "sqrt");
    check(UnOp::Sin, "sin");
    check(UnOp::Cos, "cos");
    check(UnOp::Tan, "tan");
    check(UnOp::Exp, "exp");
    check(UnOp::Log, "log");
    check(UnOp::Ln, "ln");
    check(UnOp::Grad, "grad");
    check(UnOp::Div, "div");
    check(UnOp::Curl, "curl");
    check(UnOp::Laplacian, "laplacian");
    check(UnOp::Transpose, "transpose");
    check(UnOp::Conjugate, "conjugate");
    check(UnOp::Trace, "trace");
    check(UnOp::Det, "det");
}
