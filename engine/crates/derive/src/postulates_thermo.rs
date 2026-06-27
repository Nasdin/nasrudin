//! Thermodynamics postulates as `Expr`-tree axioms.
//!
//! Foundational thermodynamics, expressed as propositional `Expr` trees.
//! These cover the classical (macroscopic) thermodynamic laws plus the
//! ideal-gas equation of state. Statistical-mechanics postulates
//! (Boltzmann distribution, partition function, Boltzmann entropy)
//! live in `postulates_statmech.rs`.
//!
//! Variable conventions:
//! - `T` temperature, `S` entropy, `U` internal energy, `Q` heat,
//!   `W` work, `P` pressure, `V` volume, `n` mole number.
//!
//! Reference: H. Callen, *Thermodynamics and an Introduction to
//! Thermostatistics*, 2nd ed., Ch. 1–4.

use crate::axiom_store::{Axiom, AxiomStore};
use nasrudin_core::{BinOp, Domain, Expr, PhysConst};

impl AxiomStore {
    /// Register the foundational thermodynamics postulate set.
    pub fn load_thermodynamics_postulates(&mut self) {
        for axiom in thermodynamics_postulates() {
            self.register(axiom);
        }
    }
}

pub fn thermodynamics_postulates() -> Vec<Axiom> {
    let t = || Expr::Var("T".into());
    let s = || Expr::Var("S".into());
    let u = || Expr::Var("U".into());
    let q = || Expr::Var("Q".into());
    let w = || Expr::Var("W".into());
    let p = || Expr::Var("P".into());
    let v = || Expr::Var("V".into());
    let n = || Expr::Var("n".into());
    let r_gas = || Expr::Const(PhysConst::Boltzmann); // k_B; for molar form NA·k_B = R

    let lit = |n: i64| Expr::Lit(n, 1);
    let zero = || Expr::Lit(0, 1);
    let mul = |a: Expr, b: Expr| Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(b));
    let sub = |a: Expr, b: Expr| Expr::BinOp(BinOp::Sub, Box::new(a), Box::new(b));
    let add = |a: Expr, b: Expr| Expr::BinOp(BinOp::Add, Box::new(a), Box::new(b));
    let eq = |a: Expr, b: Expr| Expr::BinOp(BinOp::Eq, Box::new(a), Box::new(b));
    let gt = |a: Expr, b: Expr| Expr::BinOp(BinOp::Gt, Box::new(a), Box::new(b));
    let ge = |a: Expr, b: Expr| Expr::BinOp(BinOp::Ge, Box::new(a), Box::new(b));
    let du_dt = || Expr::Deriv(Box::new(u()), "t".into());
    let ds_dt = || Expr::Deriv(Box::new(s()), "t".into());
    let dq_dt = || Expr::Deriv(Box::new(q()), "t".into());
    let dw_dt = || Expr::Deriv(Box::new(w()), "t".into());

    vec![
        // Zeroth law (transitivity is structural; encode as the existence
        // of a real-valued temperature function — represented operationally
        // as `T > 0` for an equilibrium state).
        Axiom {
            name: "thermo_zeroth_law".into(),
            domain: Domain::Thermodynamics,
            statement: gt(t(), zero()),
            description: "Zeroth law: every equilibrium state has a positive empirical \
                 temperature T > 0 (Callen §1.5)."
                .into(),
        },
        // First law (rate form): dU/dt = dQ/dt - dW/dt. ΔU = Q - W in
        // integrated form; differential is more convenient for chains.
        Axiom {
            name: "thermo_first_law".into(),
            domain: Domain::Thermodynamics,
            statement: eq(du_dt(), sub(dq_dt(), dw_dt())),
            description: "First law of thermodynamics (rate form): dU/dt = dQ/dt - dW/dt. \
                 Conservation of energy in thermodynamic systems (Callen §2.1)."
                .into(),
        },
        // Second law (Clausius form, rate inequality): dS/dt ≥ 0 for
        // an isolated system.
        Axiom {
            name: "thermo_second_law".into(),
            domain: Domain::Thermodynamics,
            statement: ge(ds_dt(), zero()),
            description: "Second law (Clausius): the entropy of an isolated system never \
                 decreases, dS/dt ≥ 0 (Callen §4.6)."
                .into(),
        },
        // Third law (Nernst): S → 0 as T → 0. Encoded as the limit
        // statement S = 0 at T = 0, expressed via implication.
        Axiom {
            name: "thermo_third_law".into(),
            domain: Domain::Thermodynamics,
            statement: Expr::BinOp(
                BinOp::Implies,
                Box::new(eq(t(), zero())),
                Box::new(eq(s(), zero())),
            ),
            description: "Third law (Nernst-Planck): a perfect crystal's entropy approaches \
                 zero as T → 0 (Callen §11.1)."
                .into(),
        },
        // Reversible heat transfer: dQ = T·dS (defining relation).
        Axiom {
            name: "thermo_reversible_heat".into(),
            domain: Domain::Thermodynamics,
            statement: eq(dq_dt(), mul(t(), ds_dt())),
            description: "Reversible heat transfer (rate form): dQ/dt = T·dS/dt. Defines \
                 the thermodynamic temperature scale (Callen §3.4)."
                .into(),
        },
        // Quasistatic mechanical work: dW = P·dV (rate form).
        Axiom {
            name: "thermo_quasistatic_work".into(),
            domain: Domain::Thermodynamics,
            statement: eq(dw_dt(), mul(p(), Expr::Deriv(Box::new(v()), "t".into()))),
            description: "Quasistatic mechanical work: dW/dt = P·dV/dt. PV-work for a fluid \
                 system (Callen §1.7)."
                .into(),
        },
        // Ideal gas equation of state: P·V = n·k_B·T (here using k_B
        // rather than R; equivalent up to Avogadro factor for n in
        // particles vs moles).
        Axiom {
            name: "thermo_ideal_gas_law".into(),
            domain: Domain::Thermodynamics,
            statement: eq(mul(p(), v()), mul(mul(n(), r_gas()), t())),
            description: "Ideal gas equation of state: PV = n·k_B·T (in number-of-particles \
                 form). Captures the dilute-gas limit (Callen §3.5)."
                .into(),
        },
        // Internal energy of an ideal monoatomic gas: U = (3/2) n k_B T.
        Axiom {
            name: "thermo_ideal_monoatomic_energy".into(),
            domain: Domain::Thermodynamics,
            statement: eq(u(), mul(Expr::Lit(3, 2), mul(mul(n(), r_gas()), t()))),
            description: "Internal energy of an ideal monoatomic gas: U = (3/2) n k_B T. \
                 Equipartition over 3 translational DOF (Reif §2.1)."
                .into(),
        },
        // Enthalpy: H = U + PV (definition).
        Axiom {
            name: "thermo_enthalpy_def".into(),
            domain: Domain::Thermodynamics,
            statement: eq(Expr::Var("H".into()), add(u(), mul(p(), v()))),
            description: "Enthalpy: H = U + PV. Natural variable for constant-pressure \
                 processes (Callen §6.4)."
                .into(),
        },
        // Helmholtz free energy: F = U - TS.
        Axiom {
            name: "thermo_helmholtz_def".into(),
            domain: Domain::Thermodynamics,
            statement: eq(Expr::Var("F".into()), sub(u(), mul(t(), s()))),
            description: "Helmholtz free energy: F = U - TS. Natural variable for \
                 constant-temperature, constant-volume processes (Callen §6.4)."
                .into(),
        },
        // Gibbs free energy: G = H - TS = U + PV - TS.
        Axiom {
            name: "thermo_gibbs_def".into(),
            domain: Domain::Thermodynamics,
            statement: eq(
                Expr::Var("G".into()),
                sub(add(u(), mul(p(), v())), mul(t(), s())),
            ),
            description: "Gibbs free energy: G = U + PV - TS. Natural variable for \
                 constant-T constant-P processes; equilibrium ↔ G minimum \
                 (Callen §6.4)."
                .into(),
        },
        // Boltzmann constant positivity: k_B > 0. Convention.
        Axiom {
            name: "thermo_kb_positive".into(),
            domain: Domain::Thermodynamics,
            statement: gt(r_gas(), Expr::Lit(0, 1)),
            description: "Boltzmann constant k_B > 0. Sign convention; underpins entropy \
                 positivity and the second law."
                .into(),
        },
        // Hold n positive (sanity).
        Axiom {
            name: "thermo_n_positive".into(),
            domain: Domain::Thermodynamics,
            statement: gt(n(), zero()),
            description: "Particle number / mole count is positive: n > 0.".into(),
        },
        // Hold T positive (already in zeroth_law but explicit for chains).
        Axiom {
            name: "thermo_volume_positive".into(),
            domain: Domain::Thermodynamics,
            statement: gt(v(), Expr::Lit(0, 1)),
            description: "Volume is positive: V > 0.".into(),
        },
        // Suppress unused warnings for `lit` placeholder helpers
        Axiom {
            name: "thermo_pressure_positive".into(),
            domain: Domain::Thermodynamics,
            statement: gt(p(), lit(0)),
            description: "Pressure is positive: P > 0.".into(),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::no_cheat_audit;

    #[test]
    fn all_thermo_postulates_register() {
        let mut store = AxiomStore::new();
        store.load_thermodynamics_postulates();
        assert!(store.get("thermo_first_law").is_some());
        assert!(store.get("thermo_second_law").is_some());
        assert!(store.get("thermo_third_law").is_some());
        assert!(store.get("thermo_reversible_heat").is_some());
        assert!(store.get("thermo_ideal_gas_law").is_some());
        assert!(store.get("thermo_helmholtz_def").is_some());
        assert!(store.get("thermo_gibbs_def").is_some());
    }

    #[test]
    fn thermo_postulates_pass_no_cheat_audit() {
        let mut store = AxiomStore::new();
        store.load_thermodynamics_postulates();
        let v = no_cheat_audit::audit(&store);
        assert!(v.is_empty(), "thermodynamics postulates flagged: {v:?}");
    }

    #[test]
    fn thermo_postulates_distinct() {
        use std::collections::HashSet;
        let posts = thermodynamics_postulates();
        let canons: HashSet<String> = posts.iter().map(|a| a.statement.to_canonical()).collect();
        assert_eq!(canons.len(), posts.len());
    }
}
