//! Dimensional analysis for expressions.
//!
//! Infers physical dimensions of expressions and checks that equations
//! are dimensionally homogeneous.

use nasrudin_core::{BinOp, Dimension, Expr, PhysConst, UnOp};
use std::collections::HashMap;

/// Known dimensions for SR variables.
pub fn sr_variable_dimensions() -> HashMap<String, Dimension> {
    let mut dims = HashMap::new();
    dims.insert("E".into(), Dimension::ENERGY);
    dims.insert("m".into(), Dimension::MASS);
    dims.insert("p".into(), Dimension::MOMENTUM);
    dims.insert("v".into(), Dimension::VELOCITY);
    dims.insert("t".into(), Dimension::TIME);
    dims.insert("F".into(), Dimension::FORCE);
    dims
}

/// Known dimensions for physical constants.
pub fn constant_dimension(c: &PhysConst) -> Option<Dimension> {
    match c {
        PhysConst::SpeedOfLight => Some(Dimension::VELOCITY),
        PhysConst::PlanckConst | PhysConst::ReducedPlanck => Some(Dimension::ACTION),
        PhysConst::GravConst => {
            // G has dimensions L³/(M·T²) = L³ M⁻¹ T⁻²
            Some(Dimension::new(3, -1, -2, 0, 0, 0, 0))
        }
        PhysConst::Boltzmann => Some(Dimension::ENTROPY),
        PhysConst::ElectronMass | PhysConst::ProtonMass => Some(Dimension::MASS),
        PhysConst::ElectronCharge => Some(Dimension::CHARGE),
        PhysConst::Pi | PhysConst::EulersNumber => Some(Dimension::DIMENSIONLESS),
        PhysConst::Avogadro => {
            // mol⁻¹
            Some(Dimension::new(0, 0, 0, 0, 0, -1, 0))
        }
        PhysConst::VacuumPermittivity => {
            // C²·s²/(kg·m³) = I²·T⁴/(M·L³)
            Some(Dimension::new(-3, -1, 4, 2, 0, 0, 0))
        }
        PhysConst::VacuumPermeability => {
            // kg·m/A² = M·L·T⁻²·I⁻²
            Some(Dimension::new(1, 1, -2, -2, 0, 0, 0))
        }
    }
}

/// Infer the physical dimension of an expression.
///
/// Returns `None` if the dimension cannot be determined or is inconsistent.
pub fn infer_dimension(
    expr: &Expr,
    var_dims: &HashMap<String, Dimension>,
) -> Option<Dimension> {
    match expr {
        Expr::Var(name) => var_dims.get(name).copied(),
        Expr::Const(c) => constant_dimension(c),
        Expr::Lit(_, _) => Some(Dimension::DIMENSIONLESS),
        Expr::BinOp(op, l, r) => {
            let dl = infer_dimension(l, var_dims)?;
            let dr = infer_dimension(r, var_dims)?;
            match op {
                BinOp::Add | BinOp::Sub => {
                    if dl == dr {
                        Some(dl)
                    } else {
                        None // dimension mismatch
                    }
                }
                BinOp::Mul | BinOp::Dot | BinOp::Cross => Some(dl * dr),
                BinOp::Div => Some(dl / dr),
                BinOp::Pow => {
                    // Only handle integer literal exponents
                    if let Expr::Lit(n, 1) = r.as_ref() {
                        Some(dl.power(*n as i8))
                    } else {
                        None
                    }
                }
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    if dl == dr {
                        Some(Dimension::DIMENSIONLESS)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        Expr::UnOp(op, e) => {
            let d = infer_dimension(e, var_dims)?;
            match op {
                UnOp::Neg | UnOp::Abs => Some(d),
                UnOp::Sqrt => {
                    // sqrt halves all exponents; only valid if all even
                    let dim = d;
                    if dim.length % 2 == 0
                        && dim.mass % 2 == 0
                        && dim.time % 2 == 0
                        && dim.current % 2 == 0
                        && dim.temperature % 2 == 0
                        && dim.amount % 2 == 0
                        && dim.luminosity % 2 == 0
                    {
                        Some(Dimension::new(
                            dim.length / 2,
                            dim.mass / 2,
                            dim.time / 2,
                            dim.current / 2,
                            dim.temperature / 2,
                            dim.amount / 2,
                            dim.luminosity / 2,
                        ))
                    } else {
                        None
                    }
                }
                // Trig functions require dimensionless input, return dimensionless
                UnOp::Sin | UnOp::Cos | UnOp::Tan | UnOp::Exp | UnOp::Log | UnOp::Ln => {
                    if d.is_dimensionless() {
                        Some(Dimension::DIMENSIONLESS)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Check that an equation `lhs = rhs` is dimensionally homogeneous.
pub fn check_equation_dimensions(
    expr: &Expr,
    var_dims: &HashMap<String, Dimension>,
) -> Result<Dimension, String> {
    if let Expr::BinOp(BinOp::Eq, lhs, rhs) = expr {
        let dl = infer_dimension(lhs, var_dims)
            .ok_or_else(|| "cannot infer dimension of LHS".to_string())?;
        let dr = infer_dimension(rhs, var_dims)
            .ok_or_else(|| "cannot infer dimension of RHS".to_string())?;
        if dl == dr {
            Ok(dl)
        } else {
            Err(format!(
                "dimension mismatch: LHS has {dl}, RHS has {dr}"
            ))
        }
    } else {
        Err("expression is not an equation".to_string())
    }
}
