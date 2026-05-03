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
fn put_theorem_rejects_self_cycle() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    // T whose proof cites itself via ModusPonens — not the canonical
    // "this IS the axiom" leaf shape, which is allowed. Should reject.
    let tid = [9u8, 0, 0, 0, 0, 0, 0, 0];
    let bad = Theorem {
        id: tid,
        statement: Expr::Var("self".into()),
        canonical: "self".into(),
        latex: String::new(),
        proof: ProofTree::ModusPonens {
            premise: Box::new(ProofTree::Axiom(tid)),
            implication: Box::new(ProofTree::Axiom(tid)),
        },
        depth: 1,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: vec![tid],
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    };
    let err = db.put_theorem(&bad).unwrap_err();
    let msg = format!("{err:?}");
    assert!(
        msg.to_lowercase().contains("cycle"),
        "error must mention cycle, got: {msg}"
    );
}

#[test]
fn tactic_proof_with_parents_populates_ancestors() {
    // PhysLean-imported derived theorems land with proof =
    // ProofTree::TacticProof (opaque kernel proof term) and parents =
    // the dep list the Lean proof-walk extracted. The reverse-deps
    // index must still see the dependency edges.
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let a = axiom_theorem(1, "A");
    let b = axiom_theorem(2, "B");
    db.put_theorem(&a).unwrap();
    db.put_theorem(&b).unwrap();

    // C is opaque (TacticProof) but explicitly cites A and B via parents.
    let c_id = [3u8, 0, 0, 0, 0, 0, 0, 0];
    let c = Theorem {
        id: c_id,
        statement: Expr::Var("C".into()),
        canonical: "C".into(),
        latex: String::new(),
        proof: ProofTree::TacticProof {
            tactic: "physlean".into(),
            proof_term: vec![],
        },
        depth: 1,
        complexity: 0,
        domain: Domain::SpecialRelativity,
        dimension: None,
        parents: vec![a.id, b.id],
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Imported {
            source: "PhysLean::Test.C".into(),
        },
    };
    db.put_theorem(&c).unwrap();

    let lin_c = db.get_lineage(&c.id).unwrap().unwrap();
    let ancestors: BTreeSet<_> = lin_c.axiom_ancestors.iter().copied().collect();
    assert!(ancestors.contains(&a.id), "TacticProof child must cite A via parents");
    assert!(ancestors.contains(&b.id), "TacticProof child must cite B via parents");

    // Reverse-deps must reflect the edges, so re-deriving A excludes C.
    let forbidden_a = db.forbidden_for_target(&a.id).unwrap();
    assert!(forbidden_a.contains(&c.id));
}

#[test]
fn put_theorem_accepts_self_axiom_leaf() {
    // A leaf-axiom theorem (proof is ProofTree::Axiom(self.id)) is
    // the canonical seed pattern from island.rs. Must NOT be rejected.
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
    let a = axiom_theorem(7, "A");
    db.put_theorem(&a).expect("self-axiom-leaf must be accepted");
}

#[test]
fn backfill_populates_existing_theorems() {
    let dir = TempDir::new().unwrap();

    // Phase 1: write theorems WITH the new lineage logic, then wipe lineage
    // and reverse-deps to simulate a pre-migration db state.
    {
        let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
        let mut a = axiom_theorem(1, "A");
        a.depth = 0;
        let mut b = derived_theorem(2, "B", &[a.id]);
        b.depth = 1;
        let mut c = derived_theorem(3, "C", &[b.id]);
        c.depth = 2;
        db.put_theorem(&a).unwrap();
        db.put_theorem(&b).unwrap();
        db.put_theorem(&c).unwrap();
        db.clear_lineage_for_test().unwrap();
    }

    // Phase 2: reopen, run backfill, verify both indexes restored.
    {
        let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();
        let count = db.backfill_lineage_and_reverse_deps().unwrap();
        assert_eq!(count, 3, "backfill processed all 3 theorems");

        let a_id = [1u8, 0, 0, 0, 0, 0, 0, 0];
        let mut deps_a = db.list_dependents(&a_id).unwrap();
        deps_a.sort();
        let mut expected = vec![[2u8, 0, 0, 0, 0, 0, 0, 0], [3u8, 0, 0, 0, 0, 0, 0, 0]];
        expected.sort();
        assert_eq!(deps_a, expected);

        // Idempotent: second run produces same state, returns same count.
        let count2 = db.backfill_lineage_and_reverse_deps().unwrap();
        assert_eq!(count2, 3);
        let mut deps_a2 = db.list_dependents(&a_id).unwrap();
        deps_a2.sort();
        assert_eq!(deps_a2, expected);
    }
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
