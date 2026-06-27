//! General relativity postulates as `Expr`-tree axioms.
//!
//! Foundational GR encoded in scalar form for the chain engine.
//! GR's natural objects (metric tensor `g_μν`, Ricci `R_μν`,
//! stress-energy `T_μν`) are second-rank tensors that the flat
//! `Expr` AST cannot represent directly — there's no Symbol-indexed
//! tensor node, only the unary `BinOp::TensorProduct` for product-style
//! decomposition. We encode the headline relations as scalar axioms
//! with `Var` placeholders for tensor names. This means the chain
//! engine can introduce them by name and Lean's tensor-aware tactics
//! (mathlib's `LinearAlgebra.TensorProduct`) close the structural
//! gap at proof time.
//!
//! Variable conventions:
//! - `g_metric` the metric (treated as a single Var slot for chains)
//! - `R_ricci` the Ricci tensor scalar slot, `R_scalar` the curvature scalar
//! - `T_stress` the stress-energy tensor slot
//! - `Lambda` cosmological constant
//! - `proper_time` the τ proper-time variable
//!
//! Reference: S. Carroll, *Spacetime and Geometry*, Ch. 4 (Einstein
//! equation) + Ch. 8 (cosmology). MTW, *Gravitation*, §16.

use crate::axiom_store::{Axiom, AxiomStore};
use nasrudin_core::{BinOp, Domain, Expr, PhysConst};

impl AxiomStore {
    /// Register the foundational general-relativity postulate set.
    pub fn load_general_relativity_postulates(&mut self) {
        for axiom in general_relativity_postulates() {
            self.register(axiom);
        }
    }
}

pub fn general_relativity_postulates() -> Vec<Axiom> {
    let g = || Expr::Var("g_metric".into());
    let r_ricci = || Expr::Var("R_ricci".into());
    let r_scalar = || Expr::Var("R_scalar".into());
    let t_stress = || Expr::Var("T_stress".into());
    let lambda = || Expr::Var("Lambda".into());
    let g_einstein = || Expr::Var("G_einstein".into());
    let x_geo = || Expr::Var("x".into());
    let big_g = || Expr::Const(PhysConst::GravConst);
    let c = || Expr::Const(PhysConst::SpeedOfLight);
    let pi_const = || Expr::Const(PhysConst::Pi);

    let lit = |n: i64| Expr::Lit(n, 1);
    let zero = || Expr::Lit(0, 1);
    let mul = |a: Expr, b: Expr| Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(b));
    let sub = |a: Expr, b: Expr| Expr::BinOp(BinOp::Sub, Box::new(a), Box::new(b));
    let add = |a: Expr, b: Expr| Expr::BinOp(BinOp::Add, Box::new(a), Box::new(b));
    let div = |a: Expr, b: Expr| Expr::BinOp(BinOp::Div, Box::new(a), Box::new(b));
    let pow = |a: Expr, b: Expr| Expr::BinOp(BinOp::Pow, Box::new(a), Box::new(b));
    let eq = |a: Expr, b: Expr| Expr::BinOp(BinOp::Eq, Box::new(a), Box::new(b));
    let gt = |a: Expr, b: Expr| Expr::BinOp(BinOp::Gt, Box::new(a), Box::new(b));
    let d2_x = || {
        // d²x/dτ² — encoded as derivative of derivative.
        let dx = Expr::Deriv(Box::new(x_geo()), "proper_time".into());
        Expr::Deriv(Box::new(dx), "proper_time".into())
    };

    vec![
        // Einstein tensor definition: G = R_ricci - (1/2) g R_scalar.
        Axiom {
            name: "gr_einstein_tensor_def".into(),
            domain: Domain::GeneralRelativity,
            statement: eq(
                g_einstein(),
                sub(r_ricci(), mul(Expr::Lit(1, 2), mul(g(), r_scalar()))),
            ),
            description: "Einstein tensor (slot form): G = R_μν - (½) g_μν R. Trace-reversed \
                 Ricci tensor (Carroll §4.5)."
                .into(),
        },
        // Einstein field equations: G + Λ g = (8πG/c⁴) T.
        Axiom {
            name: "gr_einstein_field_equation".into(),
            domain: Domain::GeneralRelativity,
            statement: eq(
                add(g_einstein(), mul(lambda(), g())),
                mul(
                    div(mul(lit(8), mul(pi_const(), big_g())), pow(c(), lit(4))),
                    t_stress(),
                ),
            ),
            description: "Einstein field equations (slot form): G_μν + Λ g_μν = (8πG/c⁴) T_μν. \
                 Couples spacetime curvature to stress-energy (Carroll §4.6)."
                .into(),
        },
        // Einstein equations without cosmological constant (special case
        // useful as a chain ladder rung).
        Axiom {
            name: "gr_einstein_field_no_lambda".into(),
            domain: Domain::GeneralRelativity,
            statement: eq(
                g_einstein(),
                mul(
                    div(mul(lit(8), mul(pi_const(), big_g())), pow(c(), lit(4))),
                    t_stress(),
                ),
            ),
            description: "Einstein equations without cosmological constant: G_μν = (8πG/c⁴) T_μν. \
                 The Λ=0 case (Carroll §4.6, original 1915 form)."
                .into(),
        },
        // Geodesic equation (slot form): d²x/dτ² + Γ·(dx/dτ)² = 0,
        // encoded as d²x/dτ² = -Γ·v² where Γ = Γ_kin is a slot for
        // Christoffel symbols and v = dx/dτ.
        Axiom {
            name: "gr_geodesic_equation".into(),
            domain: Domain::GeneralRelativity,
            statement: eq(
                d2_x(),
                Expr::UnOp(
                    nasrudin_core::UnOp::Neg,
                    Box::new(mul(
                        Expr::Var("Gamma_kin".into()),
                        pow(Expr::Deriv(Box::new(x_geo()), "proper_time".into()), lit(2)),
                    )),
                ),
            ),
            description: "Geodesic equation (slot form): d²x/dτ² = -Γ (dx/dτ)². Free-fall \
                 paths in curved spacetime (Carroll §3.4)."
                .into(),
        },
        // Equivalence principle: locally, GR reduces to SR. Encoded as
        // the existence of a frame where g = η (Minkowski metric, slot
        // η_minkowski).
        Axiom {
            name: "gr_equivalence_principle".into(),
            domain: Domain::GeneralRelativity,
            statement: Expr::BinOp(
                BinOp::Implies,
                Box::new(Expr::Var("local_inertial_frame".into())),
                Box::new(eq(g(), Expr::Var("eta_minkowski".into()))),
            ),
            description: "Equivalence principle: in a local inertial frame, the metric \
                 reduces to Minkowski. Foundation of GR (Carroll §2.1)."
                .into(),
        },
        // Newtonian limit: Einstein equation reduces to Poisson. In
        // weak-field, slow-motion limit: ∇²Φ = 4πGρ. Encoded as a
        // separate axiom that's recovered as a limit case.
        Axiom {
            name: "gr_newtonian_limit_poisson".into(),
            domain: Domain::GeneralRelativity,
            statement: eq(
                Expr::UnOp(
                    nasrudin_core::UnOp::Laplacian,
                    Box::new(Expr::Var("Phi_grav".into())),
                ),
                mul(
                    mul(lit(4), pi_const()),
                    mul(big_g(), Expr::Var("rho".into())),
                ),
            ),
            description: "Newtonian limit of GR: ∇²Φ = 4πGρ. Recovered from EFE in the \
                 weak-field, slow-motion regime (Carroll §4.1)."
                .into(),
        },
        // Speed of light positive (carrying it into GR domain too).
        Axiom {
            name: "gr_c_positive".into(),
            domain: Domain::GeneralRelativity,
            statement: gt(c(), zero()),
            description: "Speed of light c > 0 in the GR domain.".into(),
        },
        // Newton's constant positive.
        Axiom {
            name: "gr_big_g_positive".into(),
            domain: Domain::GeneralRelativity,
            statement: gt(big_g(), zero()),
            description: "Newton's gravitational constant G > 0.".into(),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::no_cheat_audit;

    #[test]
    fn all_gr_postulates_register() {
        let mut store = AxiomStore::new();
        store.load_general_relativity_postulates();
        assert!(store.get("gr_einstein_tensor_def").is_some());
        assert!(store.get("gr_einstein_field_equation").is_some());
        assert!(store.get("gr_geodesic_equation").is_some());
        assert!(store.get("gr_equivalence_principle").is_some());
        assert!(store.get("gr_newtonian_limit_poisson").is_some());
    }

    #[test]
    fn gr_postulates_pass_no_cheat_audit() {
        let mut store = AxiomStore::new();
        store.load_general_relativity_postulates();
        let v = no_cheat_audit::audit(&store);
        assert!(v.is_empty(), "GR postulates flagged: {v:?}");
    }

    #[test]
    fn gr_postulates_distinct() {
        use std::collections::HashSet;
        let posts = general_relativity_postulates();
        let canons: HashSet<String> = posts.iter().map(|a| a.statement.to_canonical()).collect();
        assert_eq!(canons.len(), posts.len());
    }
}
