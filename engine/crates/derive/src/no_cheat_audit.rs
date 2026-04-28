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
use nasrudin_core::{BinOp, Expr, PhysConst};

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
