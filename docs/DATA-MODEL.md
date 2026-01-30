# Data Model Reference

## Core Types

### Expression (`Expr`)

The universal representation for all mathematical and physics expressions.

```rust
pub enum Expr {
    /// Variable: x, y, m, c, E, F
    Var(Symbol),

    /// Constant: 0, 1, 2, pi, e, c (speed of light), h (Planck)
    Const(PhysConst),

    /// Rational literal
    Lit(Rational),

    /// Function application: f(x)
    App(Box<Expr>, Box<Expr>),

    /// Lambda abstraction: λ(x : T). body
    Lam(Symbol, Box<Type>, Box<Expr>),

    /// Dependent function type: Π(x : A). B(x)
    Pi(Symbol, Box<Type>, Box<Type>),

    /// Binary operator: a + b, a * b, a = b
    BinOp(BinOperator, Box<Expr>, Box<Expr>),

    /// Unary operator: -a, |a|, ∂/∂x
    UnOp(UnOperator, Box<Expr>),

    /// Integral: ∫ f dx over [a, b]
    Integral(Box<Expr>, Symbol, Option<Box<Expr>>, Option<Box<Expr>>),

    /// Derivative: d/dx f
    Deriv(Box<Expr>, Symbol),

    /// Partial derivative: ∂/∂x f
    PartialDeriv(Box<Expr>, Symbol),

    /// Sum: Σ_{i=a}^{b} f(i)
    Sum(Box<Expr>, Symbol, Box<Expr>, Box<Expr>),

    /// Product: Π_{i=a}^{b} f(i)
    Prod(Box<Expr>, Symbol, Box<Expr>, Box<Expr>),

    /// Limit: lim_{x -> a} f(x)
    Limit(Box<Expr>, Symbol, Box<Expr>),

    /// Tensor: T^{ij}_{kl}
    Tensor(TensorExpr),

    /// Let binding: let x = e1 in e2
    Let(Symbol, Box<Expr>, Box<Expr>),
}

pub enum BinOperator {
    Add, Sub, Mul, Div, Pow,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or, Implies, Iff,
    Cross, Dot, TensorProduct,
}

pub enum UnOperator {
    Neg, Abs, Sqrt,
    Sin, Cos, Tan,
    Exp, Log, Ln,
    Grad, Div, Curl, Laplacian,
    Transpose, Conjugate, Trace, Det,
}
```

### Physical Constant (`PhysConst`)

```rust
pub enum PhysConst {
    /// Speed of light: c = 299,792,458 m/s
    SpeedOfLight,
    /// Planck constant: h = 6.626e-34 J⋅s
    PlanckConst,
    /// Reduced Planck: ħ = h / 2π
    ReducedPlanck,
    /// Gravitational: G = 6.674e-11 m³/(kg⋅s²)
    GravConst,
    /// Boltzmann: k_B = 1.381e-23 J/K
    Boltzmann,
    /// Electron charge: e = 1.602e-19 C
    ElectronCharge,
    /// Electron mass: m_e = 9.109e-31 kg
    ElectronMass,
    /// Proton mass: m_p = 1.673e-27 kg
    ProtonMass,
    /// Vacuum permittivity: ε₀
    VacuumPermittivity,
    /// Vacuum permeability: μ₀
    VacuumPermeability,
    /// Avogadro: N_A = 6.022e23 mol⁻¹
    Avogadro,
    /// Pi: π = 3.14159...
    Pi,
    /// Euler's number: e = 2.71828...
    EulersNumber,
}
```

### Dimension

SI base dimensions for dimensional analysis:

```rust
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Dimension {
    pub length: i8,      // L  (meter)
    pub mass: i8,        // M  (kilogram)
    pub time: i8,        // T  (second)
    pub current: i8,     // I  (ampere)
    pub temperature: i8, // Θ  (kelvin)
    pub amount: i8,      // N  (mole)
    pub luminosity: i8,  // J  (candela)
}

// Named dimensions
impl Dimension {
    pub const DIMENSIONLESS: Self = Self::new(0, 0, 0, 0, 0, 0, 0);
    pub const LENGTH: Self       = Self::new(1, 0, 0, 0, 0, 0, 0);
    pub const MASS: Self         = Self::new(0, 1, 0, 0, 0, 0, 0);
    pub const TIME: Self         = Self::new(0, 0, 1, 0, 0, 0, 0);
    pub const VELOCITY: Self     = Self::new(1, 0, -1, 0, 0, 0, 0);
    pub const ACCELERATION: Self = Self::new(1, 0, -2, 0, 0, 0, 0);
    pub const FORCE: Self        = Self::new(1, 1, -2, 0, 0, 0, 0);
    pub const ENERGY: Self       = Self::new(2, 1, -2, 0, 0, 0, 0);
    pub const POWER: Self        = Self::new(2, 1, -3, 0, 0, 0, 0);
    pub const MOMENTUM: Self     = Self::new(1, 1, -1, 0, 0, 0, 0);
    pub const PRESSURE: Self     = Self::new(-1, 1, -2, 0, 0, 0, 0);
    pub const CHARGE: Self       = Self::new(0, 0, 1, 1, 0, 0, 0);
    pub const VOLTAGE: Self      = Self::new(2, 1, -3, -1, 0, 0, 0);
    pub const ENTROPY: Self      = Self::new(2, 1, -2, 0, -1, 0, 0);
    pub const ACTION: Self       = Self::new(2, 1, -1, 0, 0, 0, 0); // J⋅s
}
```

### Theorem

```rust
pub struct Theorem {
    /// Unique identifier: xxHash64 of canonical prefix notation
    pub id: TheoremId,

    /// The proposition being stated
    pub statement: Expr,

    /// Canonical prefix notation (for hashing/dedup)
    pub canonical: String,

    /// LaTeX rendering of the statement
    pub latex: String,

    /// The full proof derivation tree
    pub proof: ProofTree,

    /// Number of inference steps from axioms
    pub depth: u32,

    /// Kolmogorov-inspired complexity (AST node count)
    pub complexity: u32,

    /// Physics domain classification
    pub domain: Domain,

    /// Dimensional type of the statement (if applicable)
    pub dimension: Option<Dimension>,

    /// IDs of theorems used in the proof
    pub parents: Vec<TheoremId>,

    /// IDs of theorems that use this one (populated lazily)
    pub children: Vec<TheoremId>,

    /// Lean4 verification status
    pub verified: VerificationStatus,

    /// Multi-objective fitness score
    pub fitness: FitnessScore,

    /// GA generation when this was created
    pub generation: u64,

    /// Timestamp of creation
    pub created_at: u64,

    /// Which GA operator produced this
    pub origin: TheoremOrigin,
}

pub type TheoremId = [u8; 8]; // xxHash64

pub enum VerificationStatus {
    Pending,
    Verified { proof_term: Vec<u8>, tactic_used: String },
    Rejected { reason: String },
    Timeout,
}

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

pub enum TheoremOrigin {
    Axiom,
    Imported { source: String },
    Crossover { parent_a: TheoremId, parent_b: TheoremId },
    Mutation { parent: TheoremId, operator: String },
    Simplification { parent: TheoremId },
    DomainTransfer { parent: TheoremId, from: Domain, to: Domain },
}
```

### Proof Tree

```rust
pub enum ProofTree {
    /// Leaf: an axiom or previously proven theorem
    Axiom(TheoremId),

    /// Modus ponens: from P and P->Q, derive Q
    ModusPonens {
        premise: Box<ProofTree>,
        implication: Box<ProofTree>,
    },

    /// Universal instantiation: from ∀x.P(x), derive P(t)
    UnivInst {
        universal: Box<ProofTree>,
        term: Expr,
    },

    /// Substitution: replace variable with expression
    Substitute {
        source: Box<ProofTree>,
        var: Symbol,
        replacement: Expr,
    },

    /// Equational rewrite: from a=b, rewrite f(a) to f(b)
    Rewrite {
        equation: Box<ProofTree>,
        target: Box<ProofTree>,
        position: Vec<usize>, // path in AST to rewrite point
    },

    /// Chain of equalities: a = b = c = ...
    EqChain(Vec<ProofTree>),

    /// Lean4 tactic proof (opaque, verified by Lean)
    TacticProof {
        tactic: String,
        proof_term: Vec<u8>,
    },

    /// Algebraic manipulation (ring/field operations)
    Algebraic {
        source: Box<ProofTree>,
        operations: Vec<AlgebraicOp>,
    },
}

pub enum AlgebraicOp {
    AddBothSides(Expr),
    MultiplyBothSides(Expr),
    DivideBothSides(Expr),
    SquareBothSides,
    TakeSquareRoot,
    Factor,
    Expand,
    CollectTerms(Symbol),
}
```

### Fitness Score

```rust
pub struct FitnessScore {
    /// Semantic distance from K nearest neighbors in population
    /// Higher = more novel
    pub novelty: f64,

    /// Inverse of AST node count (simpler = higher)
    /// Implements Occam's razor / MDL principle
    pub complexity: f64,

    /// Inverse of derivation depth (shallower = more fundamental)
    pub depth: f64,

    /// 1.0 if dimensionally consistent, 0.0 if not
    /// Binary filter — inconsistent expressions are never stored
    pub dimensional: f64,

    /// Score for Lorentz/gauge/rotational/translational invariance
    pub symmetry: f64,

    /// Number of existing theorems connected (normalized)
    pub connectivity: f64,

    /// Pattern matching against known physics structures
    /// (does NOT reveal target theorems to the system)
    pub physics_relevance: f64,
}
```

---

## Database Schema

### RocksDB Column Families (Theorem Engine)

| CF Name | Key Format | Value Format | Purpose |
|---------|-----------|--------------|---------|
| `theorems` | `[8B hash]` | Protobuf TheoremRecord | Primary theorem store |
| `proofs` | `[8B theorem_id]` | Protobuf ProofTree | Proof derivation trees |
| `lineage` | `[8B theorem_id]` | Protobuf LineageRecord | Parent/child relationships |
| `by_domain` | `[1B domain][4B complexity][8B id]` | `[8B theorem_id]` | Domain + complexity index |
| `by_depth` | `[4B depth][8B id]` | `[8B theorem_id]` | Depth index |
| `by_axiom` | `[8B axiom_id][8B id]` | `[8B theorem_id]` | Axiom usage index |
| `by_generation` | `[8B gen][8B id]` | `[8B theorem_id]` | Generation index |
| `latex_index` | `[normalized LaTeX]` | `[8B theorem_id]` | LaTeX search index |
| `stats` | `[string key]` | `[8B value]` | Counters and metadata |

### PostgreSQL Tables (User-Facing Data)

| Table | Columns | Purpose |
|-------|---------|---------|
| `users` | id (UUID PK), email (UNIQUE), password (bcrypt), display_name, created_at | User accounts |
| `sessions` | id (UUID PK), user_id (FK→users), token (UNIQUE), expires_at, created_at | Auth sessions |
| `saved_searches` | id (UUID PK), user_id (FK→users), latex, label, created_at | Bookmarked formulas |
| `user_preferences` | user_id (UUID PK FK→users), preferences (JSONB) | Theme, filters, defaults |
| `workers` | id (TEXT PK), name, host, last_seen, theorems_contributed, status | Distributed worker registry |

---

## API Response Types

### Auth Types

```typescript
interface User {
  id: string;
  email: string;
  display_name: string | null;
  created_at: number;
}

interface AuthResponse {
  user: User;
  token: string;
  expires_at: number;
}

interface SavedSearch {
  id: string;
  latex: string;
  label: string | null;
  created_at: number;
}

interface WorkerInfo {
  id: string;
  name: string | null;
  host: string | null;
  last_seen: number;
  theorems_contributed: number;
  status: 'active' | 'inactive' | 'disconnected';
}

interface IngestBatch {
  worker_id: string;
  theorems: VerifiedTheorem[];
}

interface IngestResult {
  inserted: number;
  duplicates: number;
}
```

### Theorem Types

### TheoremResponse

```typescript
interface TheoremResponse {
  id: string;                    // hex-encoded 8-byte hash
  statement: string;             // canonical prefix notation
  latex: string;                 // LaTeX rendering
  domain: Domain;
  depth: number;
  complexity: number;
  fitness: FitnessScore;
  verified: boolean;
  generation: number;
  created_at: number;            // unix timestamp
  origin: TheoremOrigin;
  parent_ids: string[];
  child_count: number;
}
```

### LineageResponse

```typescript
interface LineageResponse {
  theorem: TheoremResponse;
  parents: TheoremResponse[];     // direct parents
  children: TheoremResponse[];    // direct children
  axiom_roots: TheoremResponse[]; // transitive axiom ancestors
}
```

### GraphResponse (for React Flow)

```typescript
interface GraphResponse {
  nodes: GraphNode[];
  edges: GraphEdge[];
}

interface GraphNode {
  id: string;
  data: {
    theorem: TheoremResponse;
    expanded: boolean;
  };
  position: { x: number; y: number }; // dagre-computed
  type: 'theorem' | 'axiom';
}

interface GraphEdge {
  id: string;
  source: string;          // parent theorem ID
  target: string;          // child theorem ID
  label?: string;          // inference rule name
  type: 'derivation';
}
```

### StatsResponse

```typescript
interface StatsResponse {
  total_theorems: number;
  verified_count: number;
  rejected_count: number;
  pending_count: number;
  generation: number;
  theorems_per_second: number;
  uptime_seconds: number;
  domain_counts: Record<Domain, number>;
  depth_histogram: number[];    // count per depth level
}
```

### DiscoveryEvent (SSE)

```typescript
interface DiscoveryEvent {
  type: 'new_theorem' | 'milestone' | 'stats_update';
  theorem?: TheoremResponse;
  message?: string;
  stats?: Partial<StatsResponse>;
}
```
