//! End-to-end: stash a derived theorem in the TheoremDb, then build a
//! derivation context for that target id and confirm the forbidden-set
//! threading lands in the context.

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
fn context_for_target_excludes_dependents_of_target() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let target_id = axiom_id_from_name("rest_energy");
    let target = stub_theorem(target_id, "rest_energy", &[], 0);
    db.put_theorem(&target).unwrap();

    // mass_shell_condition cited the target in its (stub) proof — i.e.
    // mass_shell is downstream of rest_energy in this fixture.
    let ms_id = axiom_id_from_name("mass_shell_condition");
    let ms = stub_theorem(ms_id, "mass_shell_condition", &[target_id], 1);
    db.put_theorem(&ms).unwrap();

    let engine = DerivationEngine::new();
    let ctx = engine.context_for_target(&target_id, &db).unwrap();
    let forbidden = ctx.forbidden_axioms();

    assert!(forbidden.contains(&target_id));
    assert!(forbidden.contains(&ms_id));
}
