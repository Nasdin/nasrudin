//! No-cheat audit: hard-fails when a known headline result has snuck
//! into the AxiomStore as a starting block.
//!
//! The point of the rediscover-physics POC is that E=mc² (and other
//! headline results) emerge from genuinely upstream axioms via the GA's
//! search, not because the answer was sitting in the corpus. This audit
//! is the safety net: it walks the AxiomStore and matches each axiom's
//! canonical statement against a deny-list of known headline results.
//! Boot fails loudly if any match.
//!
//! Run on:
//! - `physics-api` boot, after `load_from_catalog` + upstream layering.
//! - Worker startup, after `seed-sync` folds in peer theorems.
//!
//! Adding new entries to `forbidden_canonical_statements` is intentional
//! — every entry is a target the system is supposed to *derive*.

use crate::axiom_store::AxiomStore;
use nasrudin_core::{BinOp, Expr, PhysConst, UnOp};

/// Build the deny-list of canonical-form statements that must never
/// appear as starting axioms. Each entry is constructed as the same
/// `Expr` tree the GA / chain firewall would produce, then converted
/// to the canonical-form string via `to_canonical()`.
pub fn forbidden_canonical_statements() -> Vec<(&'static str, String)> {
    let e = || Expr::Var("E".into());
    let m = || Expr::Var("m".into());
    let p = || Expr::Var("p".into());
    let c = || Expr::Const(PhysConst::SpeedOfLight);
    let two = || Expr::Lit(2, 1);
    let four = || Expr::Lit(4, 1);
    let pow = |a: Expr, b: Expr| Expr::BinOp(BinOp::Pow, Box::new(a), Box::new(b));
    let mul = |a: Expr, b: Expr| Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(b));
    let add = |a: Expr, b: Expr| Expr::BinOp(BinOp::Add, Box::new(a), Box::new(b));
    let sub = |a: Expr, b: Expr| Expr::BinOp(BinOp::Sub, Box::new(a), Box::new(b));
    let eq = |a: Expr, b: Expr| Expr::BinOp(BinOp::Eq, Box::new(a), Box::new(b));

    let mut out = Vec::new();

    // E = m·c²
    let mc2 = mul(m(), pow(c(), two()));
    out.push(("emc2", eq(e(), mc2.clone()).to_canonical()));

    // E² = (m·c²)² (rest energy squared — direct precursor)
    out.push(("e_sq_eq_mc2_sq", eq(pow(e(), two()), pow(mc2.clone(), two())).to_canonical()));

    // Mass-shell: E² − p²c² = (mc²)²  AND  E² = (mc²)² + (pc)²
    let pc_sq = pow(mul(p(), c()), two());
    out.push((
        "mass_shell_sub",
        eq(sub(pow(e(), two()), pc_sq.clone()), pow(mc2.clone(), two())).to_canonical(),
    ));
    out.push((
        "mass_shell_add",
        eq(pow(e(), two()), add(pow(mc2.clone(), two()), pc_sq.clone())).to_canonical(),
    ));

    // Mass-shell with c⁴ on the RHS expansion
    out.push((
        "mass_shell_c4",
        eq(
            pow(e(), two()),
            add(mul(pow(p(), two()), pow(c(), two())), mul(pow(m(), two()), pow(c(), four()))),
        )
        .to_canonical(),
    ));

    // Photon dispersion: Eγ = c·p (with conventional name `Eph` /
    // photon_energy_momentum_relation). We forbid the simpler scalar
    // form here; the SR-domain symbolic version uses Eph.
    out.push(("photon_E_eq_pc", eq(e(), mul(c(), p())).to_canonical()));

    // ── Quantum mechanics headline results ──────────────────────────
    //
    // These are derivation *targets*, not postulates. They share the
    // structural shape of a final theorem the GA should rediscover from
    // the foundational QM postulates. (The postulates themselves use
    // different shapes: e.g. Schrödinger is `iℏ ∂ψ/∂t = Ĥψ`, while
    // the derived "free particle dispersion" is `E = p²/(2m)`.)
    let hbar = || Expr::Const(PhysConst::ReducedPlanck);
    let div = |a: Expr, b: Expr| Expr::BinOp(BinOp::Div, Box::new(a), Box::new(b));
    let abs = |e: Expr| Expr::UnOp(UnOp::Abs, Box::new(e));

    // Free-particle dispersion: E = p²/(2m). Direct consequence of the
    // free-particle Hamiltonian + momentum operator squared.
    out.push((
        "qm_free_particle_dispersion",
        eq(
            e(),
            div(pow(p(), two()), mul(two(), Expr::Var("m".into()))),
        )
        .to_canonical(),
    ));

    // Heisenberg uncertainty (textbook form): Δx·Δp ≥ ℏ/2.
    // Encoded as the equality boundary case (the GA derives this from
    // [x,p]=iℏ via Robertson-Schrödinger; we forbid the boundary as a
    // raw axiom).
    let dx = || Expr::Var("Delta_x".into());
    let dp = || Expr::Var("Delta_p".into());
    out.push((
        "qm_heisenberg_uncertainty_minimum",
        Expr::BinOp(
            BinOp::Eq,
            Box::new(mul(dx(), dp())),
            Box::new(div(hbar(), two())),
        )
        .to_canonical(),
    ));

    // Harmonic oscillator energy levels: Eₙ = ℏω(n + ½).
    // Derived from Schrödinger + ladder-operator algebra.
    let omega = || Expr::Var("omega".into());
    let n = || Expr::Var("n".into());
    let half = || Expr::Lit(1, 2);
    let n_plus_half = Expr::BinOp(BinOp::Add, Box::new(n()), Box::new(half()));
    out.push((
        "qm_harmonic_oscillator_levels",
        eq(e(), mul(mul(hbar(), omega()), n_plus_half)).to_canonical(),
    ));

    // de Broglie relation: λ = h/p (Planck rather than ℏ here, with
    // h_planck as a Const slot. ReducedPlanck = h/2π so the canonical
    // form differs.)
    let h = || Expr::Const(PhysConst::PlanckConst);
    out.push((
        "qm_de_broglie_wavelength",
        eq(Expr::Var("lambda".into()), div(h(), p())).to_canonical(),
    ));

    // Planck-Einstein relation: E = h ν (or ℏ ω). Forbid both forms.
    out.push((
        "qm_planck_einstein_omega",
        eq(e(), mul(hbar(), omega())).to_canonical(),
    ));
    let nu = || Expr::Var("nu".into());
    out.push((
        "qm_planck_einstein_nu",
        eq(e(), mul(h(), nu())).to_canonical(),
    ));

    // Born rule expectation: ⟨A⟩ = ⟨ψ|Â|ψ⟩. This is the *derived*
    // expectation form; the postulate is the simpler P = |c|².
    let _ = abs; // silence warning if unused

    // ── Thermodynamics headline results ─────────────────────────────
    //
    // Boltzmann entropy: S = k_B ln(Ω). NOTE: this is also one of the
    // statmech *postulates* — listing it here as a forbidden headline
    // would cause the postulate set to fail the audit. We do NOT
    // include it; statmech_boltzmann_entropy is a foundational input.
    //
    // Carnot efficiency: η = 1 - T_c/T_h (derived).
    let t_c = || Expr::Var("T_cold".into());
    let t_h = || Expr::Var("T_hot".into());
    let eta = || Expr::Var("eta".into());
    out.push((
        "thermo_carnot_efficiency",
        eq(eta(), sub(Expr::Lit(1, 1), div(t_c(), t_h()))).to_canonical(),
    ));

    // Maxwell-Boltzmann energy distribution (per particle, scalar form):
    // <E> = (3/2) k_B T. Derived; not a postulate.
    let kb = || Expr::Const(PhysConst::Boltzmann);
    out.push((
        "thermo_kinetic_energy_avg",
        eq(
            Expr::Var("E_avg".into()),
            mul(Expr::Lit(3, 2), mul(kb(), Expr::Var("T".into()))),
        )
        .to_canonical(),
    ));

    // ── General relativity headline results ─────────────────────────
    //
    // Schwarzschild radius: r_s = 2GM/c². Derived from the
    // Schwarzschild-metric solution to the EFE.
    let r_s = || Expr::Var("r_schwarzschild".into());
    let big_m = || Expr::Var("M".into());
    let big_g = || Expr::Const(PhysConst::GravConst);
    out.push((
        "gr_schwarzschild_radius",
        eq(
            r_s(),
            div(mul(two(), mul(big_g(), big_m())), pow(c(), Expr::Lit(2, 1))),
        )
        .to_canonical(),
    ));

    // Hubble's law: v = H_0 · d. Derived from FRW cosmology.
    let h0 = || Expr::Var("H_0".into());
    let d = || Expr::Var("d".into());
    out.push((
        "gr_hubble_law",
        eq(Expr::Var("v_recession".into()), mul(h0(), d())).to_canonical(),
    ));

    out
}

/// Walk the AxiomStore and panic-style-error if any axiom's canonical
/// matches a forbidden entry. Returns the list of violations (empty
/// means clean).
///
/// Callers should treat a non-empty return as a hard boot failure.
#[must_use]
pub fn audit(store: &AxiomStore) -> Vec<AuditViolation> {
    let forbidden = forbidden_canonical_statements();
    let mut violations = Vec::new();
    for axiom in store.iter() {
        let canon = axiom.statement.to_canonical();
        for (label, denied) in &forbidden {
            if canon == *denied {
                violations.push(AuditViolation {
                    axiom_name: axiom.name.clone(),
                    forbidden_label: (*label).to_string(),
                    canonical: canon.clone(),
                });
            }
        }
    }
    violations
}

/// One detected leak: a registered axiom whose statement matches a
/// known headline result.
#[derive(Debug, Clone)]
pub struct AuditViolation {
    pub axiom_name: String,
    pub forbidden_label: String,
    pub canonical: String,
}

impl std::fmt::Display for AuditViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "axiom `{}` matches forbidden headline `{}` ({})",
            self.axiom_name, self.forbidden_label, self.canonical
        )
    }
}

/// Convenience: run the audit and panic with a multi-line message
/// listing every violation. Use this from `main` so the error is loud.
pub fn audit_or_panic(store: &AxiomStore, context: &str) {
    let violations = audit(store);
    if !violations.is_empty() {
        eprintln!("\n✗ NO-CHEAT AUDIT FAILED [{context}] — refusing to boot.");
        eprintln!("  The following AxiomStore entries match known headline results:");
        for v in &violations {
            eprintln!("    • {v}");
        }
        eprintln!("  Headline results must be *derived* by the GA, not registered.");
        eprintln!("  Remove these entries (or fix the loader that registered them) before retrying.\n");
        std::process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_core::Domain;

    #[test]
    fn empty_store_passes() {
        let store = AxiomStore::new();
        assert!(audit(&store).is_empty());
    }

    #[test]
    fn upstream_sr_passes() {
        let mut store = AxiomStore::new();
        store.load_special_relativity_upstream();
        let v = audit(&store);
        assert!(
            v.is_empty(),
            "upstream SR axioms must not include the headline; got: {:?}",
            v
        );
    }

    #[test]
    fn registering_emc2_fails_audit() {
        let mut store = AxiomStore::new();
        let e = Expr::Var("E".into());
        let m = Expr::Var("m".into());
        let c = Expr::Const(PhysConst::SpeedOfLight);
        let two = Expr::Lit(2, 1);
        let mc2 = Expr::BinOp(
            BinOp::Mul,
            Box::new(m),
            Box::new(Expr::BinOp(BinOp::Pow, Box::new(c), Box::new(two))),
        );
        let stmt = Expr::BinOp(BinOp::Eq, Box::new(e), Box::new(mc2));
        store.register(crate::axiom_store::Axiom {
            name: "emc2_smuggled".into(),
            domain: Domain::SpecialRelativity,
            statement: stmt,
            description: "should be caught".into(),
        });
        let v = audit(&store);
        assert_eq!(v.len(), 1);
        assert_eq!(v[0].forbidden_label, "emc2");
    }
}
