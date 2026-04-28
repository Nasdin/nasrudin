use crate::dimension::Dimension;
use crate::expr::Expr;
use serde::{Deserialize, Serialize};
use std::fmt;

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

impl fmt::Display for Domain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Domain::PureMath => write!(f, "pure_math"),
            Domain::ClassicalMechanics => write!(f, "classical_mechanics"),
            Domain::Electromagnetism => write!(f, "electromagnetism"),
            Domain::SpecialRelativity => write!(f, "special_relativity"),
            Domain::GeneralRelativity => write!(f, "general_relativity"),
            Domain::QuantumMechanics => write!(f, "quantum_mechanics"),
            Domain::QuantumFieldTheory => write!(f, "quantum_field_theory"),
            Domain::StatisticalMechanics => write!(f, "statistical_mechanics"),
            Domain::Thermodynamics => write!(f, "thermodynamics"),
            Domain::Optics => write!(f, "optics"),
            Domain::FluidDynamics => write!(f, "fluid_dynamics"),
            Domain::CrossDomain(domains) => {
                let keys: Vec<String> = domains.iter().map(|d| d.to_string()).collect();
                write!(f, "cross:{}", keys.join("+"))
            }
        }
    }
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
    pub nasrudin_relevance: f64,
    /// Tree-edit similarity to a configured target Expr shape, in [0,1].
    /// 0 when no target is set; ~1 when the candidate's Expr matches the
    /// target structure (same root op, same symbol set, same topology).
    /// Used by the GA to bias the search toward a specific theorem we
    /// want to rediscover (e.g. E=mc²) without ever putting that
    /// theorem in the AxiomStore. See nasrudin_ga::target.
    #[serde(default)]
    pub target_shape: f64,
    /// Maximum partial match against any rung of a configured sub-goal
    /// ladder, in [0,1]. 0 when no ladder is configured. Lets the GA
    /// score chains that reach an intermediate result on the way to
    /// the headline target — e.g. a chain reaching `E² = (mc²)²` on
    /// the path to `E = mc²` gets credit for that rung even though it
    /// hasn't taken the final root.
    #[serde(default)]
    pub ladder_progress: f64,
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
            nasrudin_relevance: 0.0,
            target_shape: 0.0,
            ladder_progress: 0.0,
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
