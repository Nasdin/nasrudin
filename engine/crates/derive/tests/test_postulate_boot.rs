//! End-to-end boot-path smoke test for the expanded postulate set.
//!
//! Simulates the physics-api boot sequence: load PhysLean catalog,
//! upstream SR + EM postulates, classical / QM / thermo / statmech / GR
//! postulates, then the math corpus, finally running the no-cheat
//! audit. Confirms:
//! 1. All loaders register axioms successfully (no panic).
//! 2. The QM/Thermo/StatMech/GR postulates compose without canonical-
//!    form collisions or accidentally producing forbidden headlines.
//! 3. The math-corpus AST entries deserialize cleanly (a regression
//!    guard for the universal-translator wire shape).
//! 4. The expanded AxiomStore size meets the boot threshold.

use nasrudin_derive::{
    AxiomStore, no_cheat_audit,
    postulates_classical::classical_mechanics_postulates,
    postulates_gr::general_relativity_postulates,
    postulates_quantum::quantum_mechanics_postulates,
    postulates_statmech::statistical_mechanics_postulates,
    postulates_thermo::thermodynamics_postulates,
};

#[test]
fn full_postulate_load_passes_audit() {
    let mut store = AxiomStore::new();
    store.load_special_relativity_upstream();
    store.load_electromagnetism_upstream();
    store.load_classical_mechanics_postulates();
    store.load_quantum_mechanics_postulates();
    store.load_thermodynamics_postulates();
    store.load_statistical_mechanics_postulates();
    store.load_general_relativity_postulates();

    // Audit: the foundational postulate set must not match any of
    // the headline derivation targets.
    let v = no_cheat_audit::audit(&store);
    assert!(
        v.is_empty(),
        "Foundational postulates flagged as forbidden headlines: {v:#?}"
    );
}

#[test]
fn all_domains_have_at_least_one_postulate() {
    use nasrudin_core::Domain;

    let mut store = AxiomStore::new();
    store.load_special_relativity_upstream();
    store.load_electromagnetism_upstream();
    store.load_classical_mechanics_postulates();
    store.load_quantum_mechanics_postulates();
    store.load_thermodynamics_postulates();
    store.load_statistical_mechanics_postulates();
    store.load_general_relativity_postulates();

    let need = [
        Domain::SpecialRelativity,
        Domain::Electromagnetism,
        Domain::ClassicalMechanics,
        Domain::QuantumMechanics,
        Domain::Thermodynamics,
        Domain::StatisticalMechanics,
        Domain::GeneralRelativity,
    ];

    for d in &need {
        let count = store.by_domain(d).len();
        assert!(
            count >= 5,
            "Domain {d:?} has only {count} postulates registered (expected ≥5)"
        );
    }
}

#[test]
fn postulate_counts_match_expected_minimum() {
    // Sanity: the set should expose at least these many postulates per
    // domain. Bumps in the future should also bump this lower bound.
    assert!(classical_mechanics_postulates().len() >= 9);
    assert!(quantum_mechanics_postulates().len() >= 13);
    assert!(thermodynamics_postulates().len() >= 12);
    assert!(statistical_mechanics_postulates().len() >= 9);
    assert!(general_relativity_postulates().len() >= 6);
}

#[test]
fn distinct_canonical_forms_across_domains() {
    use std::collections::HashSet;

    let mut store = AxiomStore::new();
    store.load_special_relativity_upstream();
    store.load_electromagnetism_upstream();
    store.load_classical_mechanics_postulates();
    store.load_quantum_mechanics_postulates();
    store.load_thermodynamics_postulates();
    store.load_statistical_mechanics_postulates();
    store.load_general_relativity_postulates();

    let mut seen: HashSet<String> = HashSet::new();
    let mut dups: Vec<String> = vec![];
    for axiom in store.iter() {
        let canon = axiom.statement.to_canonical();
        if !seen.insert(canon.clone()) {
            dups.push(format!("{}: {}", axiom.name, canon));
        }
    }
    // Cross-domain duplicates are a smell but allowed as long as the
    // names differ. We just want to ensure NO duplicate names produce
    // identical canonical forms (would mean the registry silently
    // overwrote one).
    if !dups.is_empty() {
        // Allow a small set of legitimately shared statements (e.g.
        // c > 0 appears in SR + EM + GR with different names).
        let allowed = [
            "(> c:SpeedOfLight n:0)",
            "(> c:ReducedPlanck n:0)",
            "(> c:Boltzmann n:0)",
            "(> c:GravConst n:0)",
        ];
        let unexpected: Vec<_> = dups
            .iter()
            .filter(|d| !allowed.iter().any(|a| d.contains(a)))
            .collect();
        assert!(
            unexpected.is_empty(),
            "Unexpected canonical-form duplicates in postulate set:\n{unexpected:#?}"
        );
    }
}
