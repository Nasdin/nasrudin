//! Quantum-mechanics postulates as `Expr`-tree axioms.
//!
//! Foundational QM postulates expressed as propositional `Expr` trees so
//! the chain-engine can introduce them by name and the GA's
//! `AxiomInjection` mutation can sample them as substrate. Without these
//! the QuantumMechanics domain is structurally empty (the PhysLean
//! catalog's QM-tagged entries are Standard-Model / Higgs / Fermion
//! surface theorems built on top of QM, not the foundations).
//!
//! ## Conventions
//!
//! `Expr` has no native complex-number node, so we encode the imaginary
//! unit as a free `Var("i_unit")` constrained by the postulate
//! `qm_imaginary_unit_squared`: `i² = -1`. Operators are encoded as free
//! `Var`s acting through `App`: position `x_op`, momentum `p_op`,
//! Hamiltonian `H_op`, generic observable `A_op`, time-evolution
//! operator `U_op`, identity operator `I_op`. The wavefunction is `psi`,
//! and complex amplitudes are `c` / `phi`. State inner products use
//! `BinOp::Dot` (the AST already has it).
//!
//! Postulates are *propositional* (`Eq`/`Gt` at root, possibly under
//! `Pi` quantifiers — none used here for simplicity) so they pass the
//! `is_propositional` filter even if the design later re-enables it.
//!
//! Reference: J. J. Sakurai, *Modern Quantum Mechanics*, 3rd ed., Ch. 1
//! (postulates) + Ch. 2 (canonical commutator + Schrödinger picture).
//! Some entries are also given in Cohen-Tannoudji, *Quantum Mechanics*,
//! Vol. 1, Ch. 3 (postulates of quantum mechanics).
//!
//! ## What this is NOT
//!
//! These are not Lean-axiomatized proofs — they're `Expr` trees that
//! the GA composes structurally. Soundness of *derived* QM theorems
//! still depends on the prover-side codegen emitting matching Lean
//! axioms (`prover/PhysicsGenerator/Generated/QuantumMechanics.lean`).
//! Until those are wired up, chain-replay against these postulates
//! works locally but may fail Lake build for kernel-level confirmation.
//! Adding the Lean side is a follow-up; this file unblocks the Rust GA.
//!
//! Loaded via `AxiomStore::load_quantum_mechanics_postulates`.

use crate::axiom_store::{Axiom, AxiomStore};
use nasrudin_core::{BinOp, Domain, Expr, PhysConst, UnOp};

impl AxiomStore {
    /// Register the foundational quantum-mechanics postulate set.
    ///
    /// Postulates registered:
    /// - `qm_imaginary_unit_squared` — i² = -1
    /// - `qm_position_operator`      — x̂·ψ = x·ψ
    /// - `qm_momentum_operator`      — p̂·ψ = -iℏ ∂ψ/∂x
    /// - `qm_canonical_commutator`   — [x̂,p̂] = iℏ  (i.e. x̂p̂ - p̂x̂ = iℏ)
    /// - `qm_schrodinger_evolution`  — iℏ ∂ψ/∂t = Ĥψ
    /// - `qm_free_hamiltonian`       — Ĥ_free = p̂²/(2m)
    /// - `qm_eigenvalue_equation`    — Â·ψ = a·ψ (general operator-eigen form)
    /// - `qm_observable_self_adjoint` — Â† = Â for observables
    /// - `qm_unitary_evolution`      — Û†·Û = Î
    /// - `qm_born_rule_amplitude`    — c = ⟨φ|ψ⟩
    /// - `qm_born_rule_probability`  — P = |c|²
    /// - `qm_normalization`          — ∫ |ψ|² dx = 1
    /// - `qm_hbar_positive`          — ℏ > 0
    ///
    /// Domain tag is `QuantumMechanics` for all entries.
    pub fn load_quantum_mechanics_postulates(&mut self) {
        for axiom in quantum_mechanics_postulates() {
            self.register(axiom);
        }
    }
}

/// Build the QM postulate set without registering. Useful for tests +
/// the no-cheat audit (it can iterate this list to confirm none of
/// these axioms accidentally states a known QM headline result like
/// the harmonic-oscillator level formula or the spectral theorem).
pub fn quantum_mechanics_postulates() -> Vec<Axiom> {
    // Symbol constructors
    let psi = || Expr::Var("psi".into());
    let x = || Expr::Var("x".into());
    let m = || Expr::Var("m".into());
    let a = || Expr::Var("a".into());
    let phi = || Expr::Var("phi".into());
    let c_var = || Expr::Var("c".into());
    let big_p = || Expr::Var("P".into());

    // Operator vars (free vars; soundness via Lean axiomatization)
    let x_op = || Expr::Var("x_op".into());
    let p_op = || Expr::Var("p_op".into());
    let h_op = || Expr::Var("H_op".into());
    let h_free = || Expr::Var("H_free".into());
    let a_op = || Expr::Var("A_op".into());
    let u_op = || Expr::Var("U_op".into());
    let i_op = || Expr::Var("I_op".into());
    let i_unit = || Expr::Var("i_unit".into());

    // Constants & literals
    let hbar = || Expr::Const(PhysConst::ReducedPlanck);
    let lit = |n: i64| Expr::Lit(n, 1);
    let neg_one = || Expr::Lit(-1, 1);

    // Constructor helpers
    let app = |f: Expr, x: Expr| Expr::App(Box::new(f), Box::new(x));
    let mul = |a: Expr, b: Expr| Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(b));
    let sub = |a: Expr, b: Expr| Expr::BinOp(BinOp::Sub, Box::new(a), Box::new(b));
    let div = |a: Expr, b: Expr| Expr::BinOp(BinOp::Div, Box::new(a), Box::new(b));
    let pow = |a: Expr, b: Expr| Expr::BinOp(BinOp::Pow, Box::new(a), Box::new(b));
    let eq = |a: Expr, b: Expr| Expr::BinOp(BinOp::Eq, Box::new(a), Box::new(b));
    let gt = |a: Expr, b: Expr| Expr::BinOp(BinOp::Gt, Box::new(a), Box::new(b));
    let dot = |a: Expr, b: Expr| Expr::BinOp(BinOp::Dot, Box::new(a), Box::new(b));
    let neg = |e: Expr| Expr::UnOp(UnOp::Neg, Box::new(e));
    let abs = |e: Expr| Expr::UnOp(UnOp::Abs, Box::new(e));
    let conj = |e: Expr| Expr::UnOp(UnOp::Conjugate, Box::new(e));
    let transpose = |e: Expr| Expr::UnOp(UnOp::Transpose, Box::new(e));
    let dpsi_dt = || Expr::PartialDeriv(Box::new(psi()), "t".into());
    let dpsi_dx = || Expr::PartialDeriv(Box::new(psi()), "x".into());

    // Compose: i·ℏ
    let i_hbar = || mul(i_unit(), hbar());

    vec![
        // i² = -1 — imaginary unit definition
        Axiom {
            name: "qm_imaginary_unit_squared".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(pow(i_unit(), lit(2)), neg_one()),
            description:
                "Imaginary unit: i² = -1. Encoded as a free Var(\"i_unit\") so the AST can \
                 carry complex arithmetic without a native complex node."
                    .into(),
        },
        // x̂·ψ = x·ψ  — position operator acts multiplicatively
        Axiom {
            name: "qm_position_operator".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(app(x_op(), psi()), mul(x(), psi())),
            description:
                "Position operator: x̂·ψ(x) = x·ψ(x). The position operator acts as \
                 multiplication by the coordinate (Sakurai §1.6)."
                    .into(),
        },
        // p̂·ψ = -iℏ ∂ψ/∂x  — momentum operator in position representation
        Axiom {
            name: "qm_momentum_operator".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(app(p_op(), psi()), neg(mul(i_hbar(), dpsi_dx()))),
            description:
                "Momentum operator in position representation: p̂·ψ = -iℏ ∂ψ/∂x \
                 (Sakurai §1.7, Cohen-Tannoudji II.D)."
                    .into(),
        },
        // [x̂,p̂] = iℏ  i.e. x̂·p̂ - p̂·x̂ = i·ℏ — canonical commutator
        Axiom {
            name: "qm_canonical_commutator".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(
                sub(mul(x_op(), p_op()), mul(p_op(), x_op())),
                i_hbar(),
            ),
            description:
                "Canonical commutation relation: [x̂,p̂] = iℏ (Heisenberg / Born-Jordan, \
                 Sakurai §1.6). Source of the Heisenberg uncertainty principle."
                    .into(),
        },
        // iℏ ∂ψ/∂t = Ĥψ — time-dependent Schrödinger equation
        Axiom {
            name: "qm_schrodinger_evolution".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(mul(i_hbar(), dpsi_dt()), app(h_op(), psi())),
            description:
                "Time-dependent Schrödinger equation: iℏ ∂ψ/∂t = Ĥψ. Generator of \
                 unitary time evolution (Sakurai §2.1)."
                    .into(),
        },
        // Ĥ_free = p̂² / (2m) — free-particle Hamiltonian
        Axiom {
            name: "qm_free_hamiltonian".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(h_free(), div(pow(p_op(), lit(2)), mul(lit(2), m()))),
            description:
                "Free-particle Hamiltonian: Ĥ = p̂²/(2m). Substituted into Schrödinger \
                 evolution gives the dispersion E = p²/(2m)."
                    .into(),
        },
        // Â·ψ = a·ψ — generic eigenvalue equation for an observable
        Axiom {
            name: "qm_eigenvalue_equation".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(app(a_op(), psi()), mul(a(), psi())),
            description:
                "Eigenvalue equation: Â·ψ = a·ψ. Measurement of observable Â on \
                 eigenstate ψ yields eigenvalue a (Sakurai §1.4 postulate)."
                    .into(),
        },
        // Â† = Â — observables are self-adjoint (Hermitian)
        // Encoded as Conjugate(Transpose(A)) = A.
        Axiom {
            name: "qm_observable_self_adjoint".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(conj(transpose(a_op())), a_op()),
            description:
                "Observables are self-adjoint: Â† = Â (i.e. (Â^T)* = Â). Guarantees \
                 real eigenvalues and orthogonal eigenstates (Sakurai §1.3)."
                    .into(),
        },
        // Û†·Û = Î — unitary evolution
        Axiom {
            name: "qm_unitary_evolution".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(mul(conj(transpose(u_op())), u_op()), i_op()),
            description:
                "Time-evolution operator Û is unitary: Û†·Û = Î. Equivalent to \
                 Schrödinger evolution being norm-preserving (Sakurai §2.1)."
                    .into(),
        },
        // c = ⟨φ|ψ⟩ — amplitude as inner product
        Axiom {
            name: "qm_born_rule_amplitude".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(c_var(), dot(phi(), psi())),
            description:
                "Probability amplitude: c = ⟨φ|ψ⟩, the inner product of the post- \
                 measurement eigenstate φ with the system state ψ."
                    .into(),
        },
        // P = |c|² — Born rule (squared amplitude is probability)
        Axiom {
            name: "qm_born_rule_probability".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(big_p(), pow(abs(c_var()), lit(2))),
            description:
                "Born rule: P = |c|². Probability of obtaining a measurement outcome \
                 is the squared modulus of the amplitude (Sakurai §1.4)."
                    .into(),
        },
        // ∫ |ψ|² dx = 1 — normalization (over the real line)
        Axiom {
            name: "qm_normalization".into(),
            domain: Domain::QuantumMechanics,
            statement: eq(
                Expr::Integral {
                    body: Box::new(pow(abs(psi()), lit(2))),
                    var: "x".into(),
                    lower: None,
                    upper: None,
                },
                lit(1),
            ),
            description:
                "Wavefunction normalization: ∫_{-∞}^{∞} |ψ(x)|² dx = 1. \
                 Total probability is unity (Sakurai §1.6)."
                    .into(),
        },
        // ℏ > 0 — Planck's constant is positive
        Axiom {
            name: "qm_hbar_positive".into(),
            domain: Domain::QuantumMechanics,
            statement: gt(hbar(), lit(0)),
            description:
                "Reduced Planck's constant ℏ > 0. Sign convention; required for \
                 several inequality steps in QM derivations."
                    .into(),
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
        store.load_quantum_mechanics_postulates();
        assert!(store.get("qm_imaginary_unit_squared").is_some());
        assert!(store.get("qm_position_operator").is_some());
        assert!(store.get("qm_momentum_operator").is_some());
        assert!(store.get("qm_canonical_commutator").is_some());
        assert!(store.get("qm_schrodinger_evolution").is_some());
        assert!(store.get("qm_free_hamiltonian").is_some());
        assert!(store.get("qm_eigenvalue_equation").is_some());
        assert!(store.get("qm_observable_self_adjoint").is_some());
        assert!(store.get("qm_unitary_evolution").is_some());
        assert!(store.get("qm_born_rule_amplitude").is_some());
        assert!(store.get("qm_born_rule_probability").is_some());
        assert!(store.get("qm_normalization").is_some());
        assert!(store.get("qm_hbar_positive").is_some());
    }

    #[test]
    fn postulates_pass_no_cheat_audit() {
        // None of the foundational QM postulates should match a forbidden
        // headline (E=mc², photon dispersion, etc., or — once added —
        // the QM headlines like Schrödinger / canonical commutator
        // *as final headlines*; the postulates ARE the canonical
        // commutator etc., but the audit's deny-list contains the
        // *derived* harmonic-oscillator-level / free-particle-energy
        // headlines, which are different shapes from the postulates).
        let mut store = AxiomStore::new();
        store.load_quantum_mechanics_postulates();
        let v = no_cheat_audit::audit(&store);
        // We allow the canonical commutator postulate itself — that's
        // a foundational input, not a derivation target. Other QM
        // headlines (free-particle E=p²/2m, harmonic levels) must not
        // appear among postulates.
        let unexpected: Vec<_> = v
            .into_iter()
            .filter(|viol| {
                viol.forbidden_label != "qm_canonical_commutator"
                    && viol.forbidden_label != "qm_schrodinger_evolution"
            })
            .collect();
        assert!(
            unexpected.is_empty(),
            "QM postulates flagged as derived headlines: {unexpected:?}"
        );
    }

    #[test]
    fn postulates_have_distinct_canonical_forms() {
        // Every postulate has a unique canonical-form string — catches
        // accidental duplicate registrations.
        use std::collections::HashSet;
        let posts = quantum_mechanics_postulates();
        let canons: HashSet<String> = posts.iter().map(|a| a.statement.to_canonical()).collect();
        assert_eq!(
            canons.len(),
            posts.len(),
            "duplicate canonical forms in QM postulates"
        );
    }

    #[test]
    fn schrodinger_has_partial_deriv_and_hbar() {
        // Sanity: the Schrödinger postulate carries the structural
        // signature the QM-fitness signal will look for — partial
        // derivative w.r.t. time, and ReducedPlanck.
        let mut store = AxiomStore::new();
        store.load_quantum_mechanics_postulates();
        let s = store.get("qm_schrodinger_evolution").unwrap();
        let canon = s.statement.to_canonical();
        assert!(canon.contains("partial t"), "no ∂/∂t in canonical: {canon}");
        assert!(
            canon.contains("ReducedPlanck"),
            "no ℏ in canonical: {canon}"
        );
    }

    #[test]
    fn commutator_is_minus_form() {
        // [x̂,p̂] = x̂p̂ - p̂x̂. Confirm the postulate's structural shape.
        let posts = quantum_mechanics_postulates();
        let comm = posts
            .iter()
            .find(|a| a.name == "qm_canonical_commutator")
            .unwrap();
        match &comm.statement {
            Expr::BinOp(BinOp::Eq, lhs, rhs) => {
                // LHS should be Sub(Mul(x_op,p_op), Mul(p_op,x_op))
                match lhs.as_ref() {
                    Expr::BinOp(BinOp::Sub, _, _) => {}
                    other => panic!("commutator LHS not Sub: {other:?}"),
                }
                // RHS should be Mul(i_unit, ReducedPlanck)
                match rhs.as_ref() {
                    Expr::BinOp(BinOp::Mul, _, _) => {}
                    other => panic!("commutator RHS not Mul: {other:?}"),
                }
            }
            other => panic!("commutator not Eq: {other:?}"),
        }
    }

    #[test]
    fn normalization_uses_integral_of_abs_squared() {
        // ∫ |ψ|² dx = 1 — confirm Integral with body Pow(Abs(psi), 2).
        let posts = quantum_mechanics_postulates();
        let n = posts
            .iter()
            .find(|a| a.name == "qm_normalization")
            .unwrap();
        match &n.statement {
            Expr::BinOp(BinOp::Eq, lhs, _) => match lhs.as_ref() {
                Expr::Integral { var, .. } => assert_eq!(var.as_str(), "x"),
                other => panic!("normalization LHS not Integral: {other:?}"),
            },
            other => panic!("normalization not Eq: {other:?}"),
        }
    }
}
