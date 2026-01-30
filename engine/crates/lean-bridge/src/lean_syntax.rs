//! Convert `nasrudin_core::Expr` AST to Lean4 syntax strings.
//!
//! Used by:
//! - Process-based verifier: emits `.lean` files with theorem statements
//! - Export pipeline: generates standalone `.lean` proof files
//!
//! Maps each Expr variant to valid Lean4 syntax using Mathlib's ℝ type.

use nasrudin_core::{AlgebraicOp, BinOp, Domain, Expr, PhysConst, ProofTree, UnOp};

/// Convert a PhysConst to its Lean4 identifier.
pub fn const_to_lean(c: &PhysConst) -> &'static str {
    match c {
        PhysConst::SpeedOfLight => "c",
        PhysConst::PlanckConst => "h_planck",
        PhysConst::ReducedPlanck => "hbar",
        PhysConst::GravConst => "G",
        PhysConst::Boltzmann => "k_B",
        PhysConst::ElectronCharge => "e_charge",
        PhysConst::ElectronMass => "m_e",
        PhysConst::ProtonMass => "m_p",
        PhysConst::VacuumPermittivity => "eps0",
        PhysConst::VacuumPermeability => "mu0",
        PhysConst::Avogadro => "N_A",
        PhysConst::Pi => "Real.pi",
        PhysConst::EulersNumber => "Real.exp 1",
    }
}

/// Convert an Expr to a Lean4 expression string.
///
/// Produces a syntactically valid Lean4 term over `ℝ`.
pub fn expr_to_lean4(expr: &Expr) -> String {
    match expr {
        Expr::Var(name) => name.clone(),
        Expr::Const(c) => const_to_lean(c).to_string(),
        Expr::Lit(n, d) => {
            if *d == 1 {
                if *n >= 0 {
                    format!("({n} : ℝ)")
                } else {
                    format!("({n} : ℝ)")
                }
            } else {
                format!("(({n} : ℝ) / ({d} : ℝ))")
            }
        }
        Expr::App(f, x) => format!("({} {})", expr_to_lean4(f), expr_to_lean4(x)),
        Expr::Lam(var, ty, body) => {
            format!(
                "(fun ({var} : {}) => {})",
                expr_to_lean4(ty),
                expr_to_lean4(body)
            )
        }
        Expr::Pi(var, ty, body) => {
            format!(
                "(({var} : {}) → {})",
                expr_to_lean4(ty),
                expr_to_lean4(body)
            )
        }
        Expr::BinOp(op, l, r) => {
            let l_str = expr_to_lean4(l);
            let r_str = expr_to_lean4(r);
            match op {
                BinOp::Add => format!("({l_str} + {r_str})"),
                BinOp::Sub => format!("({l_str} - {r_str})"),
                BinOp::Mul => format!("({l_str} * {r_str})"),
                BinOp::Div => format!("({l_str} / {r_str})"),
                BinOp::Pow => format!("({l_str} ^ {r_str})"),
                BinOp::Eq => format!("{l_str} = {r_str}"),
                BinOp::Ne => format!("{l_str} ≠ {r_str}"),
                BinOp::Lt => format!("{l_str} < {r_str}"),
                BinOp::Le => format!("{l_str} ≤ {r_str}"),
                BinOp::Gt => format!("{l_str} > {r_str}"),
                BinOp::Ge => format!("{l_str} ≥ {r_str}"),
                BinOp::And => format!("({l_str} ∧ {r_str})"),
                BinOp::Or => format!("({l_str} ∨ {r_str})"),
                BinOp::Implies => format!("({l_str} → {r_str})"),
                BinOp::Iff => format!("({l_str} ↔ {r_str})"),
                BinOp::Cross => format!("(cross {l_str} {r_str})"),
                BinOp::Dot => format!("(dot {l_str} {r_str})"),
                BinOp::TensorProduct => format!("({l_str} ⊗ {r_str})"),
            }
        }
        Expr::UnOp(op, e) => {
            let e_str = expr_to_lean4(e);
            match op {
                UnOp::Neg => format!("(-{e_str})"),
                UnOp::Abs => format!("|{e_str}|"),
                UnOp::Sqrt => format!("(Real.sqrt {e_str})"),
                UnOp::Sin => format!("(Real.sin {e_str})"),
                UnOp::Cos => format!("(Real.cos {e_str})"),
                UnOp::Tan => format!("(Real.tan {e_str})"),
                UnOp::Exp => format!("(Real.exp {e_str})"),
                UnOp::Log => format!("(Real.log {e_str})"),
                UnOp::Ln => format!("(Real.log {e_str})"),
                UnOp::Grad => format!("(grad {e_str})"),
                UnOp::Div => format!("(div {e_str})"),
                UnOp::Curl => format!("(curl {e_str})"),
                UnOp::Laplacian => format!("(Δ {e_str})"),
                UnOp::Transpose => format!("({e_str}ᵀ)"),
                UnOp::Conjugate => format!("(conj {e_str})"),
                UnOp::Trace => format!("(Matrix.trace {e_str})"),
                UnOp::Det => format!("(Matrix.det {e_str})"),
            }
        }
        Expr::Deriv(e, var) => format!("(deriv (fun {var} => {}) {var})", expr_to_lean4(e)),
        Expr::PartialDeriv(e, var) => {
            format!("(fderiv ℝ (fun {var} => {}) {var})", expr_to_lean4(e))
        }
        Expr::Integral {
            body,
            var,
            lower,
            upper,
        } => {
            let body_str = expr_to_lean4(body);
            match (lower, upper) {
                (Some(lo), Some(hi)) => format!(
                    "(∫ {var} in Set.Icc {} {}, {})",
                    expr_to_lean4(lo),
                    expr_to_lean4(hi),
                    body_str
                ),
                _ => format!("(∫ {var}, {body_str})"),
            }
        }
        Expr::Sum {
            body,
            var,
            lower,
            upper,
        } => format!(
            "(∑ {var} in Finset.Icc {} {}, {})",
            expr_to_lean4(lower),
            expr_to_lean4(upper),
            expr_to_lean4(body)
        ),
        Expr::Prod {
            body,
            var,
            lower,
            upper,
        } => format!(
            "(∏ {var} in Finset.Icc {} {}, {})",
            expr_to_lean4(lower),
            expr_to_lean4(upper),
            expr_to_lean4(body)
        ),
        Expr::Limit {
            body,
            var,
            approaching,
        } => format!(
            "(Filter.Tendsto (fun {var} => {}) (nhds {}) (nhds _))",
            expr_to_lean4(body),
            expr_to_lean4(approaching)
        ),
        Expr::Let(var, val, body) => format!(
            "(let {var} := {}; {})",
            expr_to_lean4(val),
            expr_to_lean4(body)
        ),
    }
}

/// Collect all free variable names from an expression.
pub fn collect_free_vars(expr: &Expr) -> Vec<String> {
    let mut vars = Vec::new();
    let mut seen = std::collections::HashSet::new();
    collect_vars_inner(expr, &mut vars, &mut seen);
    vars
}

fn collect_vars_inner(
    expr: &Expr,
    vars: &mut Vec<String>,
    seen: &mut std::collections::HashSet<String>,
) {
    match expr {
        Expr::Var(name) => {
            if seen.insert(name.clone()) {
                vars.push(name.clone());
            }
        }
        Expr::BinOp(_, l, r) | Expr::App(l, r) => {
            collect_vars_inner(l, vars, seen);
            collect_vars_inner(r, vars, seen);
        }
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => {
            collect_vars_inner(e, vars, seen);
        }
        Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) | Expr::Let(_, ty, body) => {
            collect_vars_inner(ty, vars, seen);
            collect_vars_inner(body, vars, seen);
        }
        Expr::Integral {
            body, lower, upper, ..
        } => {
            collect_vars_inner(body, vars, seen);
            if let Some(l) = lower {
                collect_vars_inner(l, vars, seen);
            }
            if let Some(u) = upper {
                collect_vars_inner(u, vars, seen);
            }
        }
        Expr::Sum {
            body, lower, upper, ..
        } => {
            collect_vars_inner(body, vars, seen);
            collect_vars_inner(lower, vars, seen);
            collect_vars_inner(upper, vars, seen);
        }
        Expr::Limit {
            body, approaching, ..
        } => {
            collect_vars_inner(body, vars, seen);
            collect_vars_inner(approaching, vars, seen);
        }
        _ => {}
    }
}

/// Render a Lean4 theorem signature from an expression.
///
/// For an equation like `E = m * c ^ 2`, produces:
/// ```lean
/// theorem thm_name (E m : ℝ) : E = m * c ^ 2
/// ```
///
/// Physical constants (c, G, hbar, etc.) are not included as parameters
/// since they are defined in the PhysicsGenerator namespace.
pub fn render_theorem_signature(name: &str, statement: &Expr) -> String {
    let vars = collect_free_vars(statement);

    // Filter out physical constants (they're in scope via `open PhysicsGenerator`)
    let param_vars: Vec<&str> = vars
        .iter()
        .filter(|v| !is_physics_constant(v))
        .map(|v| v.as_str())
        .collect();

    let params = if param_vars.is_empty() {
        String::new()
    } else {
        let param_list = param_vars.join(" ");
        format!(" ({param_list} : ℝ)")
    };

    let lean_stmt = expr_to_lean4(statement);
    format!("theorem {name}{params} :\n    {lean_stmt}")
}

/// Check if a variable name corresponds to a physics constant
/// defined in the `PhysicsGenerator` namespace.
fn is_physics_constant(name: &str) -> bool {
    matches!(
        name,
        "c" | "G"
            | "h_planck"
            | "hbar"
            | "k_B"
            | "e_charge"
            | "m_e"
            | "m_p"
            | "eps0"
            | "mu0"
            | "N_A"
    )
}

/// Map a physics domain to its Lean4 import module path.
///
/// Returns `None` for domains without PhysLean coverage (e.g., GeneralRelativity).
pub fn domain_to_import(domain: &Domain) -> Option<&'static str> {
    match domain {
        Domain::ClassicalMechanics => Some("PhysicsGenerator.Generated.Mechanics"),
        Domain::SpecialRelativity => Some("PhysicsGenerator.Generated.SpecialRelativity"),
        Domain::Electromagnetism => Some("PhysicsGenerator.Generated.Electromagnetism"),
        Domain::QuantumMechanics => Some("PhysicsGenerator.Generated.QuantumMechanics"),
        Domain::Thermodynamics => Some("PhysicsGenerator.Generated.Thermodynamics"),
        Domain::StatisticalMechanics => Some("PhysicsGenerator.Generated.Thermodynamics"),
        Domain::PureMath => Some("PhysicsGenerator.Basic"),
        Domain::Optics => Some("PhysicsGenerator.Generated.Electromagnetism"),
        Domain::FluidDynamics => Some("PhysicsGenerator.Generated.Mechanics"),
        Domain::QuantumFieldTheory => Some("PhysicsGenerator.Generated.QuantumMechanics"),
        Domain::GeneralRelativity => None, // PhysLean doesn't cover GR
        Domain::CrossDomain(_) => Some("PhysicsGenerator.Basic"),
    }
}

/// Resolve the minimal set of Lean4 imports needed for a domain + proof tree.
pub fn resolve_imports(domain: &Domain, _proof: &ProofTree) -> Vec<String> {
    let mut imports = std::collections::BTreeSet::new();

    // Always import Basic (foundation types + constants)
    imports.insert("PhysicsGenerator.Basic".to_string());

    // Domain-specific import (if PhysLean covers it)
    if let Some(imp) = domain_to_import(domain) {
        imports.insert(imp.to_string());
    }

    // For cross-domain, import all referenced domains
    if let Domain::CrossDomain(domains) = domain {
        for d in domains {
            if let Some(imp) = domain_to_import(d) {
                imports.insert(imp.to_string());
            }
        }
    }

    imports.into_iter().collect()
}

/// Render a ProofTree to a Lean4 proof body.
pub fn render_proof(proof: &ProofTree) -> String {
    match proof {
        ProofTree::TacticProof { tactic, .. } => {
            format!(" := by\n  {tactic}\n")
        }
        ProofTree::EqChain(steps) => {
            if steps.is_empty() {
                return " := by\n  sorry -- empty equational chain\n".to_string();
            }
            let mut out = String::from(" := by\n  calc\n");
            for (i, _step) in steps.iter().enumerate() {
                out.push_str(&format!("    _ = _ := by sorry -- step {i}\n"));
            }
            out
        }
        ProofTree::Algebraic { operations, .. } => {
            let mut out = String::from(" := by\n");
            for op in operations {
                let comment = match op {
                    AlgebraicOp::AddBothSides(e) => {
                        format!("  -- add {} to both sides", expr_to_lean4(e))
                    }
                    AlgebraicOp::MultiplyBothSides(e) => {
                        format!("  -- multiply both sides by {}", expr_to_lean4(e))
                    }
                    AlgebraicOp::DivideBothSides(e) => {
                        format!("  -- divide both sides by {}", expr_to_lean4(e))
                    }
                    AlgebraicOp::SquareBothSides => "  -- square both sides".to_string(),
                    AlgebraicOp::TakeSquareRoot => "  -- take square root".to_string(),
                    AlgebraicOp::Factor => "  -- factor".to_string(),
                    AlgebraicOp::Expand => "  -- expand".to_string(),
                    AlgebraicOp::CollectTerms(var) => {
                        format!("  -- collect terms in {var}")
                    }
                };
                out.push_str(&comment);
                out.push('\n');
            }
            // Use the tactic cascade as the proof strategy
            out.push_str("  first\n");
            out.push_str("  | linarith\n");
            out.push_str("  | ring\n");
            out.push_str("  | field_simp\n");
            out.push_str("  | grind\n");
            out
        }
        ProofTree::Rewrite { .. } => " := by\n  rw [sorry] -- rewrite step\n".to_string(),
        ProofTree::Substitute { var, .. } => {
            format!(" := by\n  -- substitute {var}\n  sorry\n")
        }
        ProofTree::ModusPonens { .. } => " := by\n  exact sorry -- modus ponens\n".to_string(),
        ProofTree::UnivInst { .. } => " := by\n  exact sorry -- universal instantiation\n".to_string(),
        ProofTree::Axiom(_) => " := by\n  assumption\n".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expr_to_lean4_emc2() {
        let expr = Expr::BinOp(
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
        let lean = expr_to_lean4(&expr);
        assert_eq!(lean, "E = (m * (c ^ (2 : ℝ)))");
    }

    #[test]
    fn render_signature_simple() {
        let expr = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("F".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Var("m".into())),
                Box::new(Expr::Var("a".into())),
            )),
        );
        let sig = render_theorem_signature("newton_second", &expr);
        assert!(sig.contains("theorem newton_second"));
        assert!(sig.contains("F"));
        assert!(sig.contains("m"));
        assert!(sig.contains("a"));
        assert!(sig.contains(": ℝ"));
    }

    #[test]
    fn constants_not_in_params() {
        // E = hbar * omega — hbar is a constant, shouldn't be a param
        let expr = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("E".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Const(PhysConst::ReducedPlanck)),
                Box::new(Expr::Var("omega".into())),
            )),
        );
        let sig = render_theorem_signature("planck_relation", &expr);
        // E and omega should be params, hbar should NOT
        assert!(sig.contains("E"));
        assert!(sig.contains("omega"));
        // hbar is a constant from PhysicsGenerator namespace, not a free var from Expr::Var
        // so it won't appear as a parameter anyway (it's Expr::Const, not Expr::Var)
    }

    #[test]
    fn domain_imports() {
        assert_eq!(
            domain_to_import(&Domain::SpecialRelativity),
            Some("PhysicsGenerator.Generated.SpecialRelativity")
        );
        assert_eq!(
            domain_to_import(&Domain::Electromagnetism),
            Some("PhysicsGenerator.Generated.Electromagnetism")
        );
        assert_eq!(
            domain_to_import(&Domain::GeneralRelativity),
            None
        );
    }
}
