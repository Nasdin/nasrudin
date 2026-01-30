use nasrudin_core::{BinOp, Expr, PhysConst};
use nasrudin_derive::lean_emitter::{emit_lean_file, expr_to_lean, LeanEmitConfig};
use nasrudin_derive::DerivationEngine;

#[test]
fn test_expr_to_lean_variable() {
    assert_eq!(expr_to_lean(&Expr::Var("E".into())), "E");
    assert_eq!(expr_to_lean(&Expr::Var("m".into())), "m");
}

#[test]
fn test_expr_to_lean_constant() {
    assert_eq!(
        expr_to_lean(&Expr::Const(PhysConst::SpeedOfLight)),
        "c"
    );
    assert_eq!(
        expr_to_lean(&Expr::Const(PhysConst::PlanckConst)),
        "h_planck"
    );
}

#[test]
fn test_expr_to_lean_literal() {
    assert_eq!(expr_to_lean(&Expr::Lit(42, 1)), "42");
    assert_eq!(expr_to_lean(&Expr::Lit(0, 1)), "0");
    assert_eq!(expr_to_lean(&Expr::Lit(-3, 1)), "(-3)");
    assert_eq!(expr_to_lean(&Expr::Lit(1, 2)), "(1 / 2)");
}

#[test]
fn test_expr_to_lean_binop() {
    let e = Expr::BinOp(
        BinOp::Mul,
        Box::new(Expr::Var("m".into())),
        Box::new(Expr::BinOp(
            BinOp::Pow,
            Box::new(Expr::Const(PhysConst::SpeedOfLight)),
            Box::new(Expr::Lit(2, 1)),
        )),
    );
    let lean = expr_to_lean(&e);
    assert_eq!(lean, "(m * (c ^ 2))");
}

#[test]
fn test_expr_to_lean_equation() {
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
    let lean = expr_to_lean(&e);
    assert_eq!(lean, "E = (m * (c ^ 2))");
}

#[test]
fn test_emit_lean_file_has_correct_structure() {
    let engine = DerivationEngine::with_sr_axioms();
    let (_, ctx) = engine
        .derive_by_strategy(&nasrudin_derive::strategies::DeriveRestEnergy)
        .unwrap();

    let config = LeanEmitConfig::default();
    let lean = emit_lean_file(&ctx, &config);

    // Structure checks
    assert!(lean.contains("import Mathlib"), "missing Mathlib import");
    assert!(
        lean.contains("import PhysicsGenerator.Basic"),
        "missing Basic import"
    );
    assert!(
        lean.contains("namespace PhysicsGenerator.Derived"),
        "missing namespace"
    );
    assert!(
        lean.contains("end PhysicsGenerator.Derived"),
        "missing end namespace"
    );
    assert!(lean.contains("theorem rest_energy"), "missing theorem");
    assert!(lean.contains("ℝ"), "should use ℝ type");
}

#[test]
fn test_emit_lean_file_has_derivation_steps() {
    let engine = DerivationEngine::with_sr_axioms();
    let (_, ctx) = engine
        .derive_by_strategy(&nasrudin_derive::strategies::DeriveRestEnergy)
        .unwrap();

    let config = LeanEmitConfig::default();
    let lean = emit_lean_file(&ctx, &config);

    assert!(
        lean.contains("Derivation Steps"),
        "should include step documentation"
    );
    assert!(lean.contains("Step 1"), "should number steps");
}

#[test]
fn test_emit_lean_file_custom_config() {
    let engine = DerivationEngine::with_sr_axioms();
    let (_, ctx) = engine
        .derive_by_strategy(&nasrudin_derive::strategies::DeriveRestEnergy)
        .unwrap();

    let config = LeanEmitConfig {
        namespace: "MyProject.Physics".into(),
        theorem_name: "emc2".into(),
        use_mathlib: true,
    };
    let lean = emit_lean_file(&ctx, &config);

    assert!(lean.contains("namespace MyProject.Physics"));
    assert!(lean.contains("theorem emc2"));
    assert!(lean.contains("end MyProject.Physics"));
}
