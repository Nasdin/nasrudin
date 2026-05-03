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
use std::collections::{BTreeSet, HashSet};
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
fn forbidden_set_excludes_target_and_descendants() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // A → B → C linear chain.
    let a = axiom_theorem(1, "A");
    let b = derived_theorem(2, "B", &[a.id]);
    let c = derived_theorem(3, "C", &[b.id]);
    // D parallel: depends on A but not B or C.
    let d = derived_theorem(4, "D", &[a.id]);
    for t in [&a, &b, &c, &d] {
        db.put_theorem(t).unwrap();
    }

    // Forbidden when re-deriving A: {A, B, C, D} (everything that cites A).
    let forbidden_a = db.forbidden_for_target(&a.id).unwrap();
    let expected_a: HashSet<_> = [a.id, b.id, c.id, d.id].into_iter().collect();
    assert_eq!(forbidden_a.as_ref(), &expected_a);

    // Forbidden when re-deriving B: {B, C}. A and D still usable.
    let forbidden_b = db.forbidden_for_target(&b.id).unwrap();
    let expected_b: HashSet<_> = [b.id, c.id].into_iter().collect();
    assert_eq!(forbidden_b.as_ref(), &expected_b);

    // Forbidden when re-deriving D (a leaf): just {D}.
    let forbidden_d = db.forbidden_for_target(&d.id).unwrap();
    let expected_d: HashSet<_> = [d.id].into_iter().collect();
    assert_eq!(forbidden_d.as_ref(), &expected_d);
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
fn forbidden_cache_returns_same_arc_on_warm_lookup() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let a = axiom_theorem(1, "A");
    let b = derived_theorem(2, "B", &[a.id]);
    db.put_theorem(&a).unwrap();
    db.put_theorem(&b).unwrap();

    let f1 = db.forbidden_for_target(&a.id).unwrap();
    let f2 = db.forbidden_for_target(&a.id).unwrap();
    assert!(
        std::sync::Arc::ptr_eq(&f1, &f2),
        "cached lookup must return same Arc"
    );
}

#[test]
fn forbidden_cache_invalidates_on_new_dependent() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let a = axiom_theorem(1, "A");
    db.put_theorem(&a).unwrap();
    let f_before = db.forbidden_for_target(&a.id).unwrap();
    assert_eq!(f_before.len(), 1, "only A itself before B is added");

    // Adding B (which cites A) must invalidate A's cached entry.
    let b = derived_theorem(2, "B", &[a.id]);
    db.put_theorem(&b).unwrap();
    let f_after = db.forbidden_for_target(&a.id).unwrap();
    assert_eq!(f_after.len(), 2, "A and B after B is added");
    assert!(f_after.contains(&b.id));
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
