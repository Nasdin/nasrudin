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
}
