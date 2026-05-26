//! Regression coverage for the boot-time stats bloat that inflated
//! `domain_counts` / `total_theorems` by ~30× in prod. Two invariants:
//!
//! 1. `put_theorem` is an upsert; repeated puts of the same id MUST
//!    bump stats exactly once.
//! 2. `recompute_stats` rebuilds the persisted blob from the row store
//!    so that a corrupted/inflated stats blob can be reconciled at
//!    boot without wiping the database.

use nasrudin_core::{
    Domain, Expr, FitnessScore, ProofTree, Theorem, TheoremOrigin, VerificationStatus,
};
use nasrudin_rocks::TheoremDb;
use tempfile::TempDir;

fn axiom_theorem(id: u8, name: &str, domain: Domain) -> Theorem {
    let tid = [id, 0, 0, 0, 0, 0, 0, 0];
    Theorem {
        id: tid,
        statement: Expr::Var(name.into()),
        canonical: name.into(),
        latex: String::new(),
        proof: ProofTree::Axiom(tid),
        depth: 0,
        complexity: 0,
        domain,
        dimension: None,
        parents: vec![],
        children: vec![],
        verified: VerificationStatus::Verified {
            proof_term: vec![],
            tactic_used: "physlean".into(),
        },
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    }
}

#[test]
fn put_theorem_is_idempotent_for_stats() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let a = axiom_theorem(1, "A", Domain::PureMath);
    let b = axiom_theorem(2, "B", Domain::SpecialRelativity);

    // Initial inserts.
    db.put_theorem(&a).unwrap();
    db.put_theorem(&b).unwrap();

    // Re-inserts (mirrors boot-time PhysLean catalog re-imports). The
    // pre-fix code added +1 per call here, inflating `domain_counts`
    // by the number of boots.
    for _ in 0..30 {
        db.put_theorem(&a).unwrap();
        db.put_theorem(&b).unwrap();
    }

    let stats = db.get_stats().unwrap();
    assert_eq!(stats.total_theorems, 2, "distinct rows, not write count");
    assert_eq!(stats.total_verified, 2);
    assert_eq!(stats.domain_counts.get("pure_math"), Some(&1));
    assert_eq!(stats.domain_counts.get("special_relativity"), Some(&1));

    let by_domain = db.count_by_domain().unwrap();
    assert_eq!(by_domain.get("pure_math"), Some(&1));
    assert_eq!(by_domain.get("special_relativity"), Some(&1));
}

#[test]
fn recompute_stats_rebuilds_blob_from_rows() {
    let dir = TempDir::new().unwrap();
    let db = TheoremDb::new(dir.path().to_str().unwrap()).unwrap();

    let a = axiom_theorem(1, "A", Domain::PureMath);
    let b = axiom_theorem(2, "B", Domain::Electromagnetism);
    let c = axiom_theorem(3, "C", Domain::Electromagnetism);

    db.put_theorem(&a).unwrap();
    db.put_theorem(&b).unwrap();
    db.put_theorem(&c).unwrap();

    let recomputed = db.recompute_stats().unwrap();
    assert_eq!(recomputed.total_theorems, 3);
    assert_eq!(recomputed.total_verified, 3);
    assert_eq!(recomputed.domain_counts.get("pure_math"), Some(&1));
    assert_eq!(recomputed.domain_counts.get("electromagnetism"), Some(&2));

    // Persisted: a follow-up read sees the same values.
    let persisted = db.get_stats().unwrap();
    assert_eq!(persisted.total_theorems, 3);
    assert_eq!(persisted.domain_counts.get("electromagnetism"), Some(&2));
}
