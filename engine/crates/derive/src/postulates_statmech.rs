//! Statistical mechanics postulates as `Expr`-tree axioms.
//!
//! Bridges microstates and macroscopic thermodynamics via Boltzmann's
//! relation, the Gibbs (canonical) distribution, the partition function
//! formalism, equipartition, and the basic relations Z ↔ F ↔ U ↔ S.
//!
//! Variable conventions:
//! - `Omega` number of accessible microstates (Boltzmann's W in S=k ln Ω)
//! - `beta` thermodynamic beta = 1/(k_B T)
//! - `Z` canonical partition function
//! - `E_i`, `p_i` microstate energy / probability
//! - `S` entropy, `T` temperature, `U` mean energy, `F` Helmholtz free energy
//!
//! Reference: F. Reif, *Fundamentals of Statistical and Thermal Physics*,
//! Ch. 6–7. Pathria, *Statistical Mechanics*, 3rd ed., Ch. 3.

use crate::axiom_store::{Axiom, AxiomStore};
use nasrudin_core::{BinOp, Domain, Expr, PhysConst, UnOp};

impl AxiomStore {
    /// Register the statistical-mechanics postulate set.
    pub fn load_statistical_mechanics_postulates(&mut self) {
        for axiom in statistical_mechanics_postulates() {
            self.register(axiom);
        }
    }
}

pub fn statistical_mechanics_postulates() -> Vec<Axiom> {
    let s = || Expr::Var("S".into());
    let omega = || Expr::Var("Omega".into());
    let beta = || Expr::Var("beta".into());
    let t = || Expr::Var("T".into());
    let z = || Expr::Var("Z".into());
    let u = || Expr::Var("U".into());
    let f = || Expr::Var("F".into());
    let e_i = || Expr::Var("E_i".into());
    let p_i = || Expr::Var("p_i".into());
    let kb = || Expr::Const(PhysConst::Boltzmann);

    let lit = |n: i64| Expr::Lit(n, 1);
    let zero = || Expr::Lit(0, 1);
    let mul = |a: Expr, b: Expr| Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(b));
    let div = |a: Expr, b: Expr| Expr::BinOp(BinOp::Div, Box::new(a), Box::new(b));
    let neg_op = |e: Expr| Expr::UnOp(UnOp::Neg, Box::new(e));
    let exp_op = |e: Expr| Expr::UnOp(UnOp::Exp, Box::new(e));
    let ln_op = |e: Expr| Expr::UnOp(UnOp::Ln, Box::new(e));
    let eq = |a: Expr, b: Expr| Expr::BinOp(BinOp::Eq, Box::new(a), Box::new(b));
    let gt = |a: Expr, b: Expr| Expr::BinOp(BinOp::Gt, Box::new(a), Box::new(b));

    vec![
        // Boltzmann entropy: S = k_B ln(Ω). The headline relation
        // "S = k_B ln Ω" is in featured.rs as a UI display target,
        // but it's also a *foundational* postulate of statistical
        // mechanics — included here as a definitional axiom.
        Axiom {
            name: "statmech_boltzmann_entropy".into(),
            domain: Domain::StatisticalMechanics,
            statement: eq(s(), mul(kb(), ln_op(omega()))),
            description:
                "Boltzmann's relation: S = k_B ln(Ω). Connects microscopic state \
                 count to thermodynamic entropy (Reif §3.3)."
                    .into(),
        },
        // Beta definition: β = 1/(k_B T).
        Axiom {
            name: "statmech_beta_def".into(),
            domain: Domain::StatisticalMechanics,
            statement: eq(beta(), div(lit(1), mul(kb(), t()))),
            description:
                "Thermodynamic beta: β = 1/(k_B T). Conjugate variable to energy \
                 in the canonical ensemble (Reif §6.2)."
                    .into(),
        },
        // Gibbs distribution: p_i = exp(-β E_i) / Z. Probability of
        // microstate i in the canonical ensemble.
        Axiom {
            name: "statmech_gibbs_distribution".into(),
            domain: Domain::StatisticalMechanics,
            statement: eq(
                p_i(),
                div(exp_op(neg_op(mul(beta(), e_i()))), z()),
            ),
            description:
                "Canonical (Gibbs) distribution: p_i = exp(-β E_i) / Z. \
                 Probability of finding the system in microstate i at \
                 temperature 1/(k_B β) (Reif §6.5)."
                    .into(),
        },
        // Partition function as sum: Z = Σ exp(-β E_i). Encoded over
        // variable i.
        Axiom {
            name: "statmech_partition_function".into(),
            domain: Domain::StatisticalMechanics,
            statement: eq(
                z(),
                Expr::Sum {
                    body: Box::new(exp_op(neg_op(mul(beta(), e_i())))),
                    var: "i".into(),
                    lower: Box::new(lit(1)),
                    upper: Box::new(Expr::Var("N".into())),
                },
            ),
            description:
                "Canonical partition function: Z = Σ_i exp(-β E_i), summed over \
                 microstates (Reif §6.6)."
                    .into(),
        },
        // Free energy ↔ partition function: F = -k_B T ln Z.
        Axiom {
            name: "statmech_free_energy_partition".into(),
            domain: Domain::StatisticalMechanics,
            statement: eq(f(), neg_op(mul(mul(kb(), t()), ln_op(z())))),
            description:
                "Helmholtz free energy from partition function: F = -k_B T ln Z. \
                 Legendre transform of U (Reif §7.4, Pathria §3.5)."
                    .into(),
        },
        // Mean energy from partition function: U = -∂(ln Z)/∂β.
        Axiom {
            name: "statmech_mean_energy_partition".into(),
            domain: Domain::StatisticalMechanics,
            statement: eq(
                u(),
                neg_op(Expr::PartialDeriv(Box::new(ln_op(z())), "beta".into())),
            ),
            description:
                "Mean energy in canonical ensemble: U = -∂(ln Z)/∂β = -(1/Z)∂Z/∂β. \
                 (Reif §6.6)."
                    .into(),
        },
        // Equipartition (per quadratic DOF): ⟨½ q²⟩ = ½ k_B T.
        // Encoded as: <E_dof> = (1/2) k_B T where E_dof is a placeholder
        // variable for one quadratic-DOF energy.
        Axiom {
            name: "statmech_equipartition".into(),
            domain: Domain::StatisticalMechanics,
            statement: eq(
                Expr::Var("E_dof".into()),
                mul(Expr::Lit(1, 2), mul(kb(), t())),
            ),
            description:
                "Equipartition theorem: each quadratic degree of freedom in a \
                 classical Hamiltonian contributes ½ k_B T to the mean energy \
                 (Reif §7.5)."
                    .into(),
        },
        // Probabilities sum to 1: Σ p_i = 1.
        Axiom {
            name: "statmech_normalization".into(),
            domain: Domain::StatisticalMechanics,
            statement: eq(
                Expr::Sum {
                    body: Box::new(p_i()),
                    var: "i".into(),
                    lower: Box::new(lit(1)),
                    upper: Box::new(Expr::Var("N".into())),
                },
                lit(1),
            ),
            description:
                "Probability normalization: Σ_i p_i = 1 over all accessible \
                 microstates."
                    .into(),
        },
        // Boltzmann constant positivity (also in thermo; harmless dup).
        Axiom {
            name: "statmech_kb_positive".into(),
            domain: Domain::StatisticalMechanics,
            statement: gt(kb(), zero()),
            description: "k_B > 0 (sign convention).".into(),
        },
        // Microstate count positivity: Ω > 0 for any accessible
        // macrostate.
        Axiom {
            name: "statmech_omega_positive".into(),
            domain: Domain::StatisticalMechanics,
            statement: gt(omega(), zero()),
            description:
                "Number of accessible microstates Ω > 0 for any reachable \
                 macrostate (else entropy would be undefined)."
                    .into(),
        },
        // Beta positive (since T > 0).
        Axiom {
            name: "statmech_beta_positive".into(),
            domain: Domain::StatisticalMechanics,
            statement: gt(beta(), zero()),
            description: "Thermodynamic β > 0 (positive temperature regime).".into(),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::no_cheat_audit;

    #[test]
    fn all_statmech_postulates_register() {
        let mut store = AxiomStore::new();
        store.load_statistical_mechanics_postulates();
        assert!(store.get("statmech_boltzmann_entropy").is_some());
        assert!(store.get("statmech_gibbs_distribution").is_some());
        assert!(store.get("statmech_partition_function").is_some());
        assert!(store.get("statmech_free_energy_partition").is_some());
        assert!(store.get("statmech_mean_energy_partition").is_some());
        assert!(store.get("statmech_equipartition").is_some());
    }

    #[test]
    fn statmech_postulates_pass_no_cheat_audit() {
        let mut store = AxiomStore::new();
        store.load_statistical_mechanics_postulates();
        let v = no_cheat_audit::audit(&store);
        assert!(v.is_empty(), "statmech postulates flagged: {v:?}");
    }

    #[test]
    fn statmech_postulates_distinct() {
        use std::collections::HashSet;
        let posts = statistical_mechanics_postulates();
        let canons: HashSet<String> = posts.iter().map(|a| a.statement.to_canonical()).collect();
        assert_eq!(canons.len(), posts.len());
    }
}
