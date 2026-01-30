use physics_core::expr::*;
use physics_core::theorem::*;

#[test]
fn test_fitness_score_default() {
    let f = FitnessScore::default();
    assert_eq!(f.novelty, 0.0);
    assert_eq!(f.complexity, 0.0);
    assert_eq!(f.depth, 0.0);
    assert_eq!(f.dimensional, 0.0);
    assert_eq!(f.symmetry, 0.0);
    assert_eq!(f.connectivity, 0.0);
    assert_eq!(f.physics_relevance, 0.0);
}

#[test]
fn test_domain_serde_roundtrip() {
    let domains = vec![
        Domain::PureMath,
        Domain::ClassicalMechanics,
        Domain::QuantumMechanics,
        Domain::CrossDomain(vec![Domain::Electromagnetism, Domain::Optics]),
    ];
    for d in &domains {
        let json = serde_json::to_string(d).unwrap();
        let restored: Domain = serde_json::from_str(&json).unwrap();
        assert_eq!(*d, restored);
    }
}

#[test]
fn test_verification_status_variants() {
    let statuses: Vec<VerificationStatus> = vec![
        VerificationStatus::Pending,
        VerificationStatus::Verified {
            proof_term: vec![1, 2, 3],
            tactic_used: "ring".to_string(),
        },
        VerificationStatus::Rejected {
            reason: "type mismatch".to_string(),
        },
        VerificationStatus::Timeout,
    ];
    for s in &statuses {
        let json = serde_json::to_string(s).unwrap();
        let restored: VerificationStatus = serde_json::from_str(&json).unwrap();
        assert_eq!(*s, restored);
    }
}

#[test]
fn test_theorem_origin_variants() {
    let id_a = [1u8; 8];
    let id_b = [2u8; 8];
    let origins = vec![
        TheoremOrigin::Axiom,
        TheoremOrigin::Imported {
            source: "Newton".to_string(),
        },
        TheoremOrigin::Crossover {
            parent_a: id_a,
            parent_b: id_b,
        },
        TheoremOrigin::Mutation {
            parent: id_a,
            operator: "swap_sides".to_string(),
        },
        TheoremOrigin::Simplification { parent: id_a },
        TheoremOrigin::DomainTransfer {
            parent: id_a,
            from: Domain::ClassicalMechanics,
            to: Domain::QuantumMechanics,
        },
    ];
    for o in &origins {
        let json = serde_json::to_string(o).unwrap();
        let restored: TheoremOrigin = serde_json::from_str(&json).unwrap();
        assert_eq!(*o, restored);
    }
}

#[test]
fn test_algebraic_op_serde() {
    let ops = vec![
        AlgebraicOp::AddBothSides(Expr::Lit(1, 1)),
        AlgebraicOp::MultiplyBothSides(Expr::Var("k".into())),
        AlgebraicOp::DivideBothSides(Expr::Lit(2, 1)),
        AlgebraicOp::SquareBothSides,
        AlgebraicOp::TakeSquareRoot,
        AlgebraicOp::Factor,
        AlgebraicOp::Expand,
        AlgebraicOp::CollectTerms("x".to_string()),
    ];
    for op in &ops {
        let json = serde_json::to_string(op).unwrap();
        let restored: AlgebraicOp = serde_json::from_str(&json).unwrap();
        assert_eq!(*op, restored);
    }
}

#[test]
fn test_proof_tree_axiom() {
    let id = [0u8; 8];
    let proof = ProofTree::Axiom(id);
    let json = serde_json::to_string(&proof).unwrap();
    let _restored: ProofTree = serde_json::from_str(&json).unwrap();
    // ProofTree doesn't derive PartialEq, just check deserialization succeeds
}

#[test]
fn test_proof_tree_modus_ponens() {
    let id = [0u8; 8];
    let proof = ProofTree::ModusPonens {
        premise: Box::new(ProofTree::Axiom(id)),
        implication: Box::new(ProofTree::Axiom(id)),
    };
    let json = serde_json::to_string(&proof).unwrap();
    let _restored: ProofTree = serde_json::from_str(&json).unwrap();
}

#[test]
fn test_theorem_construction() {
    let stmt = Expr::BinOp(
        BinOp::Eq,
        Box::new(Expr::Var("E".into())),
        Box::new(Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("m".into())),
            Box::new(Expr::BinOp(
                BinOp::Pow,
                Box::new(Expr::Const(PhysConst::SpeedOfLight)),
                Box::new(Expr::Lit(2, 1)),
            )),
        )),
    );
    let canonical = stmt.to_canonical();
    let id = physics_core::compute_theorem_id(&canonical);

    let thm = Theorem {
        id,
        statement: stmt,
        canonical: canonical.clone(),
        latex: "E = mc^2".to_string(),
        proof: ProofTree::Axiom(id),
        depth: 0,
        complexity: 7,
        domain: Domain::SpecialRelativity,
        dimension: Some(physics_core::Dimension::ENERGY),
        parents: vec![],
        children: vec![],
        verified: VerificationStatus::Pending,
        fitness: FitnessScore::default(),
        generation: 0,
        created_at: 0,
        origin: TheoremOrigin::Axiom,
    };

    assert_eq!(thm.canonical, "(= v:E (* v:m (^ c:SpeedOfLight n:2)))");
    assert_eq!(thm.complexity, 7);
    assert_eq!(thm.depth, 0);

    // Serde roundtrip for the full Theorem
    let json = serde_json::to_string(&thm).unwrap();
    let restored: Theorem = serde_json::from_str(&json).unwrap();
    assert_eq!(restored.id, thm.id);
    assert_eq!(restored.canonical, thm.canonical);
    assert_eq!(restored.complexity, thm.complexity);
}
