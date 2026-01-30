use nasrudin_core::{BinOp, Dimension, Expr, PhysConst};
use nasrudin_derive::dimension_checker::{
    check_equation_dimensions, infer_dimension, sr_variable_dimensions,
};

fn var(name: &str) -> Expr {
    Expr::Var(name.into())
}

fn lit(n: i64) -> Expr {
    Expr::Lit(n, 1)
}

fn pow(base: Expr, exp: Expr) -> Expr {
    Expr::BinOp(BinOp::Pow, Box::new(base), Box::new(exp))
}

fn mul(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp::Mul, Box::new(l), Box::new(r))
}

fn add(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp::Add, Box::new(l), Box::new(r))
}

fn eq(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp::Eq, Box::new(l), Box::new(r))
}

#[test]
fn test_energy_variable_dimension() {
    let dims = sr_variable_dimensions();
    let d = infer_dimension(&var("E"), &dims);
    assert_eq!(d, Some(Dimension::ENERGY));
}

#[test]
fn test_mass_variable_dimension() {
    let dims = sr_variable_dimensions();
    let d = infer_dimension(&var("m"), &dims);
    assert_eq!(d, Some(Dimension::MASS));
}

#[test]
fn test_speed_of_light_dimension() {
    let dims = sr_variable_dimensions();
    let d = infer_dimension(&Expr::Const(PhysConst::SpeedOfLight), &dims);
    assert_eq!(d, Some(Dimension::VELOCITY));
}

#[test]
fn test_mc_squared_has_energy_dimension() {
    let dims = sr_variable_dimensions();
    let c = Expr::Const(PhysConst::SpeedOfLight);
    let c_sq = pow(c, lit(2));
    let mc_sq = mul(var("m"), c_sq);

    let d = infer_dimension(&mc_sq, &dims);
    // m * c² has dimension MASS * VELOCITY² = MASS * L²/T² = ML²T⁻² = ENERGY
    assert_eq!(d, Some(Dimension::ENERGY));
}

#[test]
fn test_e_equals_mc2_dimensionally_homogeneous() {
    let dims = sr_variable_dimensions();
    let c = Expr::Const(PhysConst::SpeedOfLight);
    let c_sq = pow(c, lit(2));
    let mc_sq = mul(var("m"), c_sq);
    let equation = eq(var("E"), mc_sq);

    let result = check_equation_dimensions(&equation, &dims);
    assert!(result.is_ok(), "E=mc² should be dimensionally homogeneous");
    assert_eq!(result.unwrap(), Dimension::ENERGY);
}

#[test]
fn test_e_equals_m_dimension_mismatch() {
    let dims = sr_variable_dimensions();
    let equation = eq(var("E"), var("m"));

    let result = check_equation_dimensions(&equation, &dims);
    assert!(result.is_err(), "E=m should fail dimensional analysis");
}

#[test]
fn test_energy_momentum_relation_dimensions() {
    let dims = sr_variable_dimensions();
    let c = Expr::Const(PhysConst::SpeedOfLight);

    // E² = p²c² + (mc²)²
    let e_sq = pow(var("E"), lit(2));
    let p_sq = pow(var("p"), lit(2));
    let c_sq = pow(c.clone(), lit(2));
    let p_sq_c_sq = mul(p_sq, c_sq.clone());
    let mc_sq = mul(var("m"), c_sq);
    let mc_sq_sq = pow(mc_sq, lit(2));
    let rhs = add(p_sq_c_sq, mc_sq_sq);
    let equation = eq(e_sq, rhs);

    let result = check_equation_dimensions(&equation, &dims);
    assert!(
        result.is_ok(),
        "E² = p²c² + (mc²)² should be dimensionally valid: {:?}",
        result
    );
    // ENERGY² dimension
    assert_eq!(result.unwrap(), Dimension::ENERGY.power(2));
}

#[test]
fn test_literal_is_dimensionless() {
    let dims = sr_variable_dimensions();
    let d = infer_dimension(&lit(42), &dims);
    assert_eq!(d, Some(Dimension::DIMENSIONLESS));
}

#[test]
fn test_pi_is_dimensionless() {
    let dims = sr_variable_dimensions();
    let d = infer_dimension(&Expr::Const(PhysConst::Pi), &dims);
    assert_eq!(d, Some(Dimension::DIMENSIONLESS));
}
