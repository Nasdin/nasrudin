//! Classical-mechanics postulates as `Expr`-tree axioms.
//!
//! PhysLean's catalog covers Lorentz / EM / SR machinery but has no
//! classical-mechanics namespace, so the kinematic ladder (`p = m·v`,
//! `F = m·a`, `KE = ½mv²`, etc.) currently has nowhere to live except
//! a small file in this crate. The "no hand-writing" rule applies to
//! *derivable* identities; it doesn't apply to *postulates* — these are
//! the irreducible base set of Newtonian mechanics, analogous to the
//! upstream SR axioms already in `axiom_store::load_special_relativity_upstream`.
//!
//! Each postulate is cited by name (Goldstein, *Classical Mechanics*, 3e,
//! or Landau-Lifshitz, vol. 1 — both standard references). When PhysLean
//! eventually ships a `PhysLean.Mechanics.Newtonian` namespace this file
//! should be removed and the upstream catalog used instead.
//!
//! Loaded via `AxiomStore::load_classical_mechanics_postulates`.

use crate::axiom_store::{Axiom, AxiomStore};
use nasrudin_core::{BinOp, Domain, Expr};

impl AxiomStore {
    /// Register the Newtonian-mechanics postulate set:
    ///
    /// - `velocity_def`         — v = dx/dt
    /// - `acceleration_def`     — a = dv/dt
    /// - `momentum_def`         — p = m·v
    /// - `newton_second`        — F = m·a       (force-mass-acceleration form)
    /// - `newton_second_dpdt`   — F = dp/dt     (rate-of-momentum form)
    /// - `kinetic_energy_def`   — KE = ½·m·v²
    /// - `gravitational_force`  — F_g = m·g     (uniform field, surface-of-Earth)
    /// - `work_def`             — W = F·d       (constant force, straight-line)
    /// - `power_def`            — P = dW/dt
    ///
    /// Reference: H. Goldstein, *Classical Mechanics*, 3rd ed., Ch. 1.
    /// Each postulate appears in §1.1–§1.4 and is treated as definitional.
    /// `newton_second_dpdt` is Newton's actual statement (Principia, Lex II);
    /// `newton_second` is the constant-mass corollary used in textbooks.
    ///
    /// Domain tag is `ClassicalMechanics` for all entries.
    pub fn load_classical_mechanics_postulates(&mut self) {
        for axiom in classical_mechanics_postulates() {
            self.register(axiom);
        }
    }
}

/// Build the postulate set without registering. Useful for tests +
/// the no-cheat audit harness (it can iterate this list to confirm
/// none of these axioms accidentally state a headline result).
pub fn classical_mechanics_postulates() -> Vec<Axiom> {
    let v = || Expr::Var("v".into());
    let x = || Expr::Var("x".into());
    let a = || Expr::Var("a".into());
    let m = || Expr::Var("m".into());
    let p = || Expr::Var("p".into());
    let f = || Expr::Var("F".into());
    let g = || Expr::Var("g".into());
    let d = || Expr::Var("d".into());
    let ke = || Expr::Var("KE".into());
    let fg = || Expr::Var("F_g".into());
    let w = || Expr::Var("W".into());
    let pow_p = || Expr::Var("P".into());

    let half = || Expr::Lit(1, 2);
    let two = || Expr::Lit(2, 1);
    let pow = |a: Expr, b: Expr| Expr::BinOp(BinOp::Pow, Box::new(a), Box::new(b));
    let mul = |a: Expr, b: Expr| Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(b));
    let eq = |a: Expr, b: Expr| Expr::BinOp(BinOp::Eq, Box::new(a), Box::new(b));
    let deriv_t = |inner: Expr| Expr::Deriv(Box::new(inner), "t".into());

    vec![
        Axiom {
            name: "velocity_def".into(),
            domain: Domain::ClassicalMechanics,
            statement: eq(v(), deriv_t(x())),
            description: "Velocity is the time derivative of position (Goldstein §1.1)".into(),
        },
        Axiom {
            name: "acceleration_def".into(),
            domain: Domain::ClassicalMechanics,
            statement: eq(a(), deriv_t(v())),
            description: "Acceleration is the time derivative of velocity (Goldstein §1.1)".into(),
        },
        Axiom {
            name: "momentum_def".into(),
            domain: Domain::ClassicalMechanics,
            statement: eq(p(), mul(m(), v())),
            description: "Linear momentum is mass times velocity (Goldstein §1.2)".into(),
        },
        Axiom {
            name: "newton_second".into(),
            domain: Domain::ClassicalMechanics,
            statement: eq(f(), mul(m(), a())),
            description:
                "Newton's second law (constant mass form): force equals mass times acceleration"
                    .into(),
        },
        Axiom {
            name: "newton_second_dpdt".into(),
            domain: Domain::ClassicalMechanics,
            statement: eq(f(), deriv_t(p())),
            description:
                "Newton's second law (Principia, Lex II): force equals rate of change of momentum"
                    .into(),
        },
        Axiom {
            name: "kinetic_energy_def".into(),
            domain: Domain::ClassicalMechanics,
            statement: eq(ke(), mul(half(), mul(m(), pow(v(), two())))),
            description: "Newtonian kinetic energy: KE = (1/2) m v² (Goldstein §1.4)".into(),
        },
        Axiom {
            name: "gravitational_force".into(),
            domain: Domain::ClassicalMechanics,
            statement: eq(fg(), mul(m(), g())),
            description:
                "Gravitational force in a uniform field (surface-of-Earth limit): F_g = m g".into(),
        },
        Axiom {
            name: "work_def".into(),
            domain: Domain::ClassicalMechanics,
            statement: eq(w(), mul(f(), d())),
            description:
                "Work for a constant force on a straight-line path: W = F·d (Goldstein §1.4)".into(),
        },
        Axiom {
            name: "power_def".into(),
            domain: Domain::ClassicalMechanics,
            statement: eq(pow_p(), deriv_t(w())),
            description: "Power is the time derivative of work done (Goldstein §1.4)".into(),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::no_cheat_audit;

    #[test]
    fn all_postulates_register() {
        let mut store = AxiomStore::new();
        store.load_classical_mechanics_postulates();
        assert!(store.get("momentum_def").is_some());
        assert!(store.get("newton_second").is_some());
        assert!(store.get("kinetic_energy_def").is_some());
        assert!(store.get("velocity_def").is_some());
        assert!(store.get("acceleration_def").is_some());
        assert!(store.get("work_def").is_some());
    }

    #[test]
    fn postulates_pass_no_cheat_audit() {
        // None of the classical-mechanics postulates should be flagged
        // as a forbidden headline. (The audit forbids E=mc², photon
        // dispersion, mass-shell — none of which involve KE / momentum
        // in the relativistic sense.)
        let mut store = AxiomStore::new();
        store.load_classical_mechanics_postulates();
        let v = no_cheat_audit::audit(&store);
        assert!(v.is_empty(), "classical postulates flagged: {v:?}");
    }

    #[test]
    fn postulates_have_distinct_canonical_forms() {
        // Every postulate should have a unique canonical-form string —
        // catches duplicate registrations.
        use std::collections::HashSet;
        let posts = classical_mechanics_postulates();
        let canons: HashSet<String> = posts.iter().map(|a| a.statement.to_canonical()).collect();
        assert_eq!(canons.len(), posts.len());
    }

    #[test]
    fn momentum_and_newton_second_compose() {
        // p = m·v  AND  F = dp/dt
        // ⇒ a worker chain that introduces both should be replayable.
        // (We don't actually do a substitution-chain here — that's the
        // GA's job. We just confirm the postulates load + canonicalize.)
        let mut store = AxiomStore::new();
        store.load_classical_mechanics_postulates();
        let p_def = store.get("momentum_def").unwrap();
        let n2_dpdt = store.get("newton_second_dpdt").unwrap();
        // p_def: Eq(p, Mul(m, v))
        match &p_def.statement {
            Expr::BinOp(BinOp::Eq, _, _) => {}
            other => panic!("momentum_def should be an Eq, got {other:?}"),
        }
        // n2_dpdt: Eq(F, Deriv(p, t))
        match &n2_dpdt.statement {
            Expr::BinOp(BinOp::Eq, _, rhs) => match rhs.as_ref() {
                Expr::Deriv(_, var) => assert_eq!(var.as_str(), "t"),
                other => panic!("rhs should be Deriv, got {other:?}"),
            },
            other => panic!("newton_second_dpdt should be Eq, got {other:?}"),
        }
    }
}
