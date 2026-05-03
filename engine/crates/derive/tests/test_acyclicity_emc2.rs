//! User-story test: `mass_shell_condition` lives in the TheoremDb as a
//! derived theorem (post-Phase-1 world). Building the derivation
//! context for an in-store E=mc² target must include
//! `mass_shell_condition` in the forbidden set, so any premise picker
//! filtering through `iter_excluding` skips it.

use nasrudin_core::{
    axiom_id_from_name, Domain, Expr, FitnessScore, ProofTree, Theorem, TheoremOrigin,
    VerificationStatus,
};
use nasrudin_derive::DerivationEngine;
use nasrudin_rocks::TheoremDb;
use tempfile::TempDir;

fn stub_theorem(
    id: nasrudin_core::TheoremId,
    name: &str,
    parents: &[nasrudin_core::TheoremId],
    depth: u32,
) -> Theorem {
    let proof = if parents.is_empty() {
        ProofTree::Axiom(id)
    } else if parents.len() == 1 {
        ProofTree::Axiom(parents[0])
    } else {
        ProofTree::EqChain(parents.iter().map(|p| ProofTree::Axiom(*p)).collect())
    };
    Theorem {
        id,
        statement: Expr::Var(name.into()),
        canonical: name.into(),
        latex: String::new(),
        proof,
        depth,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: parents.to_vec(),
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    }
}

#[test]
fn deriving_emc2_target_excludes_mass_shell_condition() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // Stash an in-store theorem at the synthetic id of "rest_energy"
    // so AxiomStore name-lookups line up with TheoremDb id-lookups.
    let target_id = axiom_id_from_name("rest_energy");
    let target = stub_theorem(target_id, "rest_energy", &[], 0);
    db.put_theorem(&target).unwrap();

    // mass_shell_condition: a (stub) derived theorem whose proof cites
    // the target. In the production world this would come from the
    // upstream-postulates derivation pipeline; for the test we hand-
    // craft the dependency edge.
    let ms_id = axiom_id_from_name("mass_shell_condition");
    let ms = stub_theorem(ms_id, "mass_shell_condition", &[target_id], 1);
    db.put_theorem(&ms).unwrap();

    // Build an engine and register a hot-tier mass_shell_condition
    // axiom so iter_excluding has something to filter against.
    let mut engine = DerivationEngine::new();
    engine.store_mut().load_special_relativity_upstream();
    engine.store_mut().register(nasrudin_derive::Axiom {
        name: "mass_shell_condition".into(),
        domain: Domain::SpecialRelativity,
        statement: Expr::Var("mass_shell_eq".into()),
        description: "stub for filter test".into(),
    });

    let ctx = engine.context_for_target(&target_id, &db).unwrap();
    let visible: Vec<String> = engine
        .store()
        .iter_excluding(ctx.forbidden_axioms())
        .map(|a| a.name)
        .collect();

    assert!(
        !visible.iter().any(|n| n == "mass_shell_condition"),
        "mass_shell_condition must be filtered out when deriving rest_energy target"
    );
    // Sanity: legitimate upstream postulates still visible.
    assert!(
        visible.iter().any(|n| n == "minkowski_invariant_def"),
        "upstream postulates must still be available"
    );
}
