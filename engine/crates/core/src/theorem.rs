use crate::dimension::Dimension;
use crate::expr::Expr;
use serde::{Deserialize, Serialize};

pub type TheoremId = [u8; 8];

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Domain {
    PureMath,
    ClassicalMechanics,
    Electromagnetism,
    SpecialRelativity,
    GeneralRelativity,
    QuantumMechanics,
    QuantumFieldTheory,
    StatisticalMechanics,
    Thermodynamics,
    Optics,
    FluidDynamics,
    CrossDomain(Vec<Domain>),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum VerificationStatus {
    Pending,
    Verified {
        proof_term: Vec<u8>,
        tactic_used: String,
    },
    Rejected {
        reason: String,
    },
    Timeout,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TheoremOrigin {
    Axiom,
    Imported {
        source: String,
    },
    Crossover {
        parent_a: TheoremId,
        parent_b: TheoremId,
    },
    Mutation {
        parent: TheoremId,
        operator: String,
    },
    Simplification {
        parent: TheoremId,
    },
    DomainTransfer {
        parent: TheoremId,
        from: Domain,
        to: Domain,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FitnessScore {
    pub novelty: f64,
    pub complexity: f64,
    pub depth: f64,
    pub dimensional: f64,
    pub symmetry: f64,
    pub connectivity: f64,
    pub physics_relevance: f64,
}

impl Default for FitnessScore {
    fn default() -> Self {
        Self {
            novelty: 0.0,
            complexity: 0.0,
            depth: 0.0,
            dimensional: 0.0,
            symmetry: 0.0,
            connectivity: 0.0,
            physics_relevance: 0.0,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Theorem {
    pub id: TheoremId,
    pub statement: Expr,
    pub canonical: String,
    pub latex: String,
    pub proof: ProofTree,
    pub depth: u32,
    pub complexity: u32,
    pub domain: Domain,
    pub dimension: Option<Dimension>,
    pub parents: Vec<TheoremId>,
    pub children: Vec<TheoremId>,
    pub verified: VerificationStatus,
    pub fitness: FitnessScore,
    pub generation: u64,
    pub created_at: u64,
    pub origin: TheoremOrigin,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum AlgebraicOp {
    AddBothSides(Expr),
    MultiplyBothSides(Expr),
    DivideBothSides(Expr),
    SquareBothSides,
    TakeSquareRoot,
    Factor,
    Expand,
    CollectTerms(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProofTree {
    Axiom(TheoremId),
    ModusPonens {
        premise: Box<ProofTree>,
        implication: Box<ProofTree>,
    },
    UnivInst {
        universal: Box<ProofTree>,
        term: Expr,
    },
    Substitute {
        source: Box<ProofTree>,
        var: String,
        replacement: Expr,
    },
    Rewrite {
        equation: Box<ProofTree>,
        target: Box<ProofTree>,
        position: Vec<usize>,
    },
    EqChain(Vec<ProofTree>),
    TacticProof {
        tactic: String,
        proof_term: Vec<u8>,
    },
    Algebraic {
        source: Box<ProofTree>,
        operations: Vec<AlgebraicOp>,
    },
}
