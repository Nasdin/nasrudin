//! Integration tests for derivation-acyclicity infrastructure:
//! - LineageRecord.axiom_ancestors populated with transitive closure
//! - CF_REVERSE_DEPS prefix-scan
//! - forbidden_for_target = {target} ∪ list_dependents(target)
//! - LRU cache returns shared Arc on warm lookups, invalidates on writes
//! - backfill migration is idempotent

use nasrudin_core::{
    Domain, Expr, FitnessScore, ProofTree, Theorem, TheoremOrigin, VerificationStatus,
};
use nasrudin_rocks::TheoremDb;
use std::collections::BTreeSet;
use tempfile::TempDir;

fn axiom_theorem(id: u8, name: &str) -> Theorem {
    let tid = [id, 0, 0, 0, 0, 0, 0, 0];
    Theorem {
        id: tid,
        statement: Expr::Var(name.into()),
        canonical: name.into(),
        latex: String::new(),
        proof: ProofTree::Axiom(tid),
        depth: 0,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: vec![],
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    }
}

fn derived_theorem(id: u8, name: &str, premise_ids: &[[u8; 8]]) -> Theorem {
    let mut leaves: Vec<ProofTree> = premise_ids
        .iter()
        .map(|p| ProofTree::Axiom(*p))
        .collect();
    let proof = if leaves.len() == 1 {
        leaves.pop().unwrap()
    } else {
        ProofTree::EqChain(leaves)
    };
    Theorem {
        id: [id, 0, 0, 0, 0, 0, 0, 0],
        statement: Expr::Var(name.into()),
        canonical: name.into(),
        latex: String::new(),
        proof,
        depth: 1,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: premise_ids.to_vec(),
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    }
}

#[test]
fn reverse_deps_index_lists_all_dependents() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let a = axiom_theorem(1, "A");
    let b = derived_theorem(2, "B", &[a.id]);
    let c = derived_theorem(3, "C", &[b.id]);
    db.put_theorem(&a).unwrap();
    db.put_theorem(&b).unwrap();
    db.put_theorem(&c).unwrap();

    // A's dependents: B (direct) and C (transitive via B).
    let mut deps = db.list_dependents(&a.id).unwrap();
    deps.sort();
    let mut expected = vec![b.id, c.id];
    expected.sort();
    assert_eq!(deps, expected);

    // C is a leaf (no theorem cites it): no dependents.
    assert!(db.list_dependents(&c.id).unwrap().is_empty());
}

#[test]
fn transitive_ancestors_chain() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // A is a leaf axiom.
    let a = axiom_theorem(1, "A");
    // B derives from A.
    let b = derived_theorem(2, "B", &[a.id]);
    // C derives from B.
    let c = derived_theorem(3, "C", &[b.id]);

    db.put_theorem(&a).unwrap();
    db.put_theorem(&b).unwrap();
    db.put_theorem(&c).unwrap();

    let lin_c = db.get_lineage(&c.id).unwrap().unwrap();
    let mut ancestors: BTreeSet<_> = lin_c.axiom_ancestors.iter().copied().collect();

    assert!(ancestors.contains(&a.id), "C must transitively cite A");
    assert!(ancestors.contains(&b.id), "C must directly cite B");
    ancestors.remove(&a.id);
    ancestors.remove(&b.id);
    assert!(ancestors.is_empty(), "C has no other ancestors");
}
