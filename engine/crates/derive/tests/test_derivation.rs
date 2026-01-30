use nasrudin_core::{BinOp, Dimension, Expr, PhysConst};
use nasrudin_derive::dimension_checker::{check_equation_dimensions, sr_variable_dimensions};
use nasrudin_derive::DerivationEngine;

#[test]
fn test_derive_rest_energy_produces_result() {
    let engine = DerivationEngine::with_sr_axioms();
    let result = engine.derive_rest_energy();

    assert!(
        result.is_ok(),
        "derivation should succeed: {:?}",
        result.err()
    );
}

#[test]
fn test_derive_rest_energy_theorem_is_e_eq_mc2() {
    let engine = DerivationEngine::with_sr_axioms();
    let result = engine.derive_rest_energy().unwrap();

    // The theorem should be E = mc²
    // As Expr: BinOp(Eq, Var("E"), BinOp(Mul, Var("m"), BinOp(Pow, Const(SpeedOfLight), Lit(2,1))))
    if let Expr::BinOp(BinOp::Eq, lhs, rhs) = &result.theorem {
        assert_eq!(**lhs, Expr::Var("E".into()));
        // RHS should be m * c²
        if let Expr::BinOp(BinOp::Mul, m, c_sq) = rhs.as_ref() {
            assert_eq!(**m, Expr::Var("m".into()));
            if let Expr::BinOp(BinOp::Pow, c, exp) = c_sq.as_ref() {
                assert_eq!(**c, Expr::Const(PhysConst::SpeedOfLight));
                assert_eq!(**exp, Expr::Lit(2, 1));
            } else {
                panic!("Expected c^2, got: {:?}", c_sq);
            }
        } else {
            panic!("Expected m * c², got: {:?}", rhs);
        }
    } else {
        panic!("Expected equation, got: {:?}", result.theorem);
    }
}

#[test]
fn test_derive_rest_energy_has_steps() {
    let engine = DerivationEngine::with_sr_axioms();
    let result = engine.derive_rest_energy().unwrap();

    // Should have multiple derivation steps
    assert!(
        result.steps.len() >= 4,
        "expected at least 4 steps, got {}",
        result.steps.len()
    );

    // First step should load the axiom
    assert!(
        result.steps[0].contains("axiom") || result.steps[0].contains("introduce"),
        "first step should introduce axiom: {}",
        result.steps[0]
    );
}

#[test]
fn test_derive_rest_energy_canonical_form() {
    let engine = DerivationEngine::with_sr_axioms();
    let result = engine.derive_rest_energy().unwrap();

    let canonical = result.theorem.to_canonical();
    // Should contain: (= v:E (* v:m (^ c:SpeedOfLight n:2)))
    assert!(
        canonical.contains("v:E") && canonical.contains("v:m") && canonical.contains("SpeedOfLight"),
        "canonical should represent E=mc²: {canonical}"
    );
}

#[test]
fn test_derive_rest_energy_dimensionally_correct() {
    let engine = DerivationEngine::with_sr_axioms();
    let result = engine.derive_rest_energy().unwrap();

    let dims = sr_variable_dimensions();
    let dim_result = check_equation_dimensions(&result.theorem, &dims);
    assert!(
        dim_result.is_ok(),
        "E=mc² should be dimensionally homogeneous: {:?}",
        dim_result.err()
    );
    assert_eq!(dim_result.unwrap(), Dimension::ENERGY);
}

#[test]
fn test_derive_rest_energy_generates_lean() {
    let engine = DerivationEngine::with_sr_axioms();
    let result = engine.derive_rest_energy().unwrap();

    let lean = &result.lean_source;
    assert!(lean.contains("import Mathlib"), "should import Mathlib");
    assert!(lean.contains("ℝ"), "should use real numbers");
    assert!(lean.contains("rest_energy"), "should name the theorem");
    assert!(
        lean.contains("Real.sqrt_sq") || lean.contains("grind") || lean.contains("simp"),
        "should contain a Mathlib tactic"
    );
}

#[test]
fn test_engine_with_sr_axioms_has_axioms() {
    let engine = DerivationEngine::with_sr_axioms();
    assert!(!engine.store().is_empty());
    assert!(engine.store().get("mass_shell_condition").is_some());
}
