//! Axiom-set extraction from a `ProofTree`.
//!
//! Walks the proof tree and collects every `Axiom(id)` leaf. Used at ingest
//! time to populate `theorems.axioms_used` deterministically and at query
//! time to answer "give me everything derivable from {axiom_a, axiom_b}".

use crate::theorem::{ProofTree, TheoremId};
use std::collections::BTreeSet;

/// Collect every axiom `TheoremId` referenced anywhere in `tree`.
///
/// `BTreeSet` because callers want deterministic iteration order (PG
/// containment queries, ingest serialization).
pub fn collect_axiom_ids(tree: &ProofTree) -> BTreeSet<TheoremId> {
    let mut out = BTreeSet::new();
    walk(tree, &mut out);
    out
}

/// 8-byte BLAKE3 prefix over the sorted axiom IDs in `set`.
///
/// Used as the second half of the 16-byte cache key for both the
/// `attempts` and `tactic_priors` column families. `BTreeSet` ordering
/// guarantees the hash is stable across calls regardless of insertion
/// order; calling with the same membership always yields the same prefix.
pub fn axiom_set_hash(set: &BTreeSet<TheoremId>) -> [u8; 8] {
    let mut hasher = blake3::Hasher::new();
    for id in set {
        hasher.update(id);
    }
    let full = hasher.finalize();
    let mut out = [0u8; 8];
    out.copy_from_slice(&full.as_bytes()[..8]);
    out
}

/// Synthetic 8-byte ID derived from a free-form axiom name.
///
/// `nasrudin_derive::AxiomStore` keys axioms by `String` name (no
/// `TheoremId` field on the `Axiom` struct). Cache code wants
/// `BTreeSet<TheoremId>` to feed into [`axiom_set_hash`], so this
/// helper provides a stable name-to-ID mapping. Same name always
/// yields the same 8 bytes; different names diverge with overwhelming
/// probability (BLAKE3, no truncation collisions in practice).
pub fn axiom_id_from_name(name: &str) -> TheoremId {
    let full = blake3::hash(name.as_bytes());
    let mut out = [0u8; 8];
    out.copy_from_slice(&full.as_bytes()[..8]);
    out
}

fn walk(tree: &ProofTree, out: &mut BTreeSet<TheoremId>) {
    match tree {
        ProofTree::Axiom(id) => {
            out.insert(*id);
        }
        ProofTree::ModusPonens { premise, implication } => {
            walk(premise, out);
            walk(implication, out);
        }
        ProofTree::UnivInst { universal, .. } => walk(universal, out),
        ProofTree::Substitute { source, .. } => walk(source, out),
        ProofTree::Rewrite { equation, target, .. } => {
            walk(equation, out);
            walk(target, out);
        }
        ProofTree::EqChain(steps) => {
            for s in steps {
                walk(s, out);
            }
        }
        ProofTree::TacticProof { .. } => {
            // A tactic proof has no upstream dependencies surfaced here.
            // If a tactic discharges via axioms, those are not represented in
            // ProofTree today; record nothing rather than fabricate an edge.
        }
        ProofTree::Algebraic { source, .. } => walk(source, out),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Expr;
    use crate::theorem::AlgebraicOp;

    fn id(n: u8) -> TheoremId {
        [n, 0, 0, 0, 0, 0, 0, 0]
    }

    #[test]
    fn single_axiom_leaf() {
        let t = ProofTree::Axiom(id(1));
        assert_eq!(collect_axiom_ids(&t), BTreeSet::from([id(1)]));
    }

    #[test]
    fn modus_ponens_combines_both_branches() {
        let t = ProofTree::ModusPonens {
            premise: Box::new(ProofTree::Axiom(id(1))),
            implication: Box::new(ProofTree::Axiom(id(2))),
        };
        assert_eq!(collect_axiom_ids(&t), BTreeSet::from([id(1), id(2)]));
    }

    #[test]
    fn eq_chain_collects_all_steps() {
        let t = ProofTree::EqChain(vec![
            ProofTree::Axiom(id(1)),
            ProofTree::Axiom(id(2)),
            ProofTree::Axiom(id(3)),
        ]);
        assert_eq!(
            collect_axiom_ids(&t),
            BTreeSet::from([id(1), id(2), id(3)])
        );
    }

    #[test]
    fn dedupes_repeated_axioms() {
        let t = ProofTree::EqChain(vec![
            ProofTree::Axiom(id(1)),
            ProofTree::Axiom(id(1)),
            ProofTree::Axiom(id(2)),
        ]);
        assert_eq!(collect_axiom_ids(&t), BTreeSet::from([id(1), id(2)]));
    }

    #[test]
    fn nested_modus_ponens() {
        let inner = ProofTree::ModusPonens {
            premise: Box::new(ProofTree::Axiom(id(3))),
            implication: Box::new(ProofTree::Axiom(id(4))),
        };
        let outer = ProofTree::ModusPonens {
            premise: Box::new(ProofTree::Axiom(id(1))),
            implication: Box::new(inner),
        };
        assert_eq!(
            collect_axiom_ids(&outer),
            BTreeSet::from([id(1), id(3), id(4)])
        );
    }

    #[test]
    fn algebraic_walks_source() {
        let t = ProofTree::Algebraic {
            source: Box::new(ProofTree::Axiom(id(7))),
            operations: vec![AlgebraicOp::SquareBothSides],
        };
        assert_eq!(collect_axiom_ids(&t), BTreeSet::from([id(7)]));
    }

    #[test]
    fn substitute_walks_source() {
        let t = ProofTree::Substitute {
            source: Box::new(ProofTree::Axiom(id(5))),
            var: "x".into(),
            replacement: Expr::Var("y".into()),
        };
        assert_eq!(collect_axiom_ids(&t), BTreeSet::from([id(5)]));
    }

    #[test]
    fn rewrite_walks_both() {
        let t = ProofTree::Rewrite {
            equation: Box::new(ProofTree::Axiom(id(1))),
            target: Box::new(ProofTree::Axiom(id(2))),
            position: vec![0, 1],
        };
        assert_eq!(collect_axiom_ids(&t), BTreeSet::from([id(1), id(2)]));
    }

    #[test]
    fn univ_inst_walks_universal() {
        let t = ProofTree::UnivInst {
            universal: Box::new(ProofTree::Axiom(id(9))),
            term: Expr::Var("x".into()),
        };
        assert_eq!(collect_axiom_ids(&t), BTreeSet::from([id(9)]));
    }

    #[test]
    fn tactic_proof_has_no_deps() {
        let t = ProofTree::TacticProof {
            tactic: "rfl".into(),
            proof_term: vec![],
        };
        assert_eq!(collect_axiom_ids(&t), BTreeSet::new());
    }

    #[test]
    fn axiom_set_hash_is_deterministic() {
        let ids = BTreeSet::from([id(1), id(2), id(3)]);
        let h1 = axiom_set_hash(&ids);
        let h2 = axiom_set_hash(&ids);
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 8);
    }

    #[test]
    fn axiom_set_hash_order_independent() {
        let mut a = BTreeSet::new();
        a.insert(id(2));
        a.insert(id(1));
        a.insert(id(3));
        let mut b = BTreeSet::new();
        b.insert(id(3));
        b.insert(id(1));
        b.insert(id(2));
        assert_eq!(axiom_set_hash(&a), axiom_set_hash(&b));
    }

    #[test]
    fn axiom_set_hash_empty_set_distinct_from_single_element() {
        let empty = BTreeSet::new();
        let one = BTreeSet::from([id(1)]);
        assert_ne!(axiom_set_hash(&empty), axiom_set_hash(&one));
    }

    #[test]
    fn axiom_set_hash_different_members_diverge() {
        let a = BTreeSet::from([id(1), id(2)]);
        let b = BTreeSet::from([id(1), id(3)]);
        assert_ne!(axiom_set_hash(&a), axiom_set_hash(&b));
    }

    #[test]
    fn axiom_id_from_name_is_deterministic() {
        let a = axiom_id_from_name("rest_frame_psq_zero");
        let b = axiom_id_from_name("rest_frame_psq_zero");
        assert_eq!(a, b);
        assert_eq!(a.len(), 8);
    }

    #[test]
    fn axiom_id_from_name_diverges_for_different_names() {
        let a = axiom_id_from_name("rest_frame_psq_zero");
        let b = axiom_id_from_name("photon_dispersion");
        assert_ne!(a, b);
    }
}
