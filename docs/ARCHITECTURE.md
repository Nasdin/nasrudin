# Architecture: Physics Generator

## System Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                         TanStack Start UI                           │
│  ┌──────────┐  ┌──────────────┐  ┌────────────┐  ┌──────────────┐ │
│  │Dashboard │  │ LaTeX Search │  │  Canvas    │  │  Domain      │ │
│  │(live     │  │ (cmdk +      │  │  Explorer  │  │  Browser     │ │
│  │ stats)   │  │  KaTeX +     │  │  (React    │  │              │ │
│  │          │  │  Fuse.js)    │  │   Flow)    │  │              │ │
│  └────┬─────┘  └──────┬───────┘  └─────┬──────┘  └──────┬───────┘ │
│       └───────────┬────┴────────────────┴────────────────┘         │
│                   │  TanStack Query + SSE + WebSocket               │
└───────────────────┼─────────────────────────────────────────────────┘
                    │ HTTP / SSE / WS
┌───────────────────┼─────────────────────────────────────────────────┐
│                   │        Axum API Server                          │
│  ┌────────────────▼──────────────────────────────────────────────┐  │
│  │  REST: /api/theorems, /search, /lineage, /auth, /ingest      │  │
│  │  SSE:  /api/events/discoveries, /events/stats                │  │
│  │  WS:   /api/ws/explore                                       │  │
│  └────────────────┬──────────────────────────────────────────────┘  │
│                   │                                                  │
│  ┌────────────────▼──────────────────────────────────────────────┐  │
│  │                    Rust GA Engine                              │  │
│  │                                                                │  │
│  │  ┌──────────┐  ┌───────────┐  ┌──────────┐  ┌─────────────┐  │  │
│  │  │Population│  │ Crossover │  │ Mutation  │  │  Selection  │  │  │
│  │  │ Manager  │  │ Operators │  │ Operators │  │  (NSGA-II)  │  │  │
│  │  └────┬─────┘  └─────┬─────┘  └────┬─────┘  └──────┬──────┘  │  │
│  │       └──────────────┴─────────────┴───────────────┘          │  │
│  │                        │          ▲                             │  │
│  │                        │          │ LLM-guided crossover       │  │
│  │                        │          │ + tactic advice             │  │
│  │  ┌─────────────────────▼──────────┴───────────────────────┐   │  │
│  │  │              Pre-filters                                │   │  │
│  │  │  • Dimensional analysis  • Type checking (fast)         │   │  │
│  │  │  • Dedup (Bloom + hash)  • Complexity bounds            │   │  │
│  │  └─────────────────────┬──────────────────────────────────┘   │  │
│  │                        │ candidates                            │  │
│  └────────────────────────┼──────────────────────────────────────┘  │
│                           │                                          │
│  ┌────────────────────────┼──────────────────────────────────────┐  │
│  │         MCP Server (physics-generator-mcp)                     │  │
│  │                                                                │  │
│  │  Tools: search_theorems, suggest_combination,                 │  │
│  │         adjust_exploration, predict_tactic, simplify, ...     │  │
│  │                                                                │  │
│  │  Connects to: RocksDB (read), GA Engine (commands),           │  │
│  │               Lean4 FFI (type-check, simplify)                │  │
│  └────────────────────────┼──────────────────────────────────────┘  │
│                           │ MCP protocol (JSON-RPC)                  │
│                   ┌───────▼───────┐                                  │
│                   │  LLM (Claude) │                                  │
│                   │               │                                  │
│                   │ • Curator     │  Runs periodically or on-demand  │
│                   │ • Crossover   │  Degrades gracefully if offline  │
│                   │ • Tactic hint │                                  │
│                   └───────────────┘                                  │
│                           │                                          │
│  ┌────────────────────────▼──────────────────────────────────────┐  │
│  │              Shared Memory (mmap ring buffer)                  │  │
│  │  ┌─────────────────────────────────────────────────────────┐  │  │
│  │  │  [candidate_1] [candidate_2] ... [candidate_N]  -->     │  │  │
│  │  │  [result_1]    [result_2]    ... [result_N]     <--     │  │  │
│  │  └─────────────────────────────────────────────────────────┘  │  │
│  └────────────────────────┬──────────────────────────────────────┘  │
│                           │                                          │
└───────────────────────────┼──────────────────────────────────────────┘
                            │ C ABI FFI
┌───────────────────────────┼──────────────────────────────────────────┐
│                           │      Lean4 Verification Workers           │
│  ┌────────────────────────▼──────────────────────────────────────┐  │
│  │  Worker Pool (N processes)                                     │  │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐     │  │
│  │  │ Worker 1 │  │ Worker 2 │  │ Worker 3 │  │ Worker N │     │  │
│  │  │ grind    │  │ simp     │  │ omega    │  │ polyrith │     │  │
│  │  │ simp     │  │ grind    │  │ ring     │  │ grind    │     │  │
│  │  │ omega    │  │ linarith │  │ grind    │  │ simp     │     │  │
│  │  └──────────┘  └──────────┘  └──────────┘  └──────────┘     │  │
│  └───────────────────────────────────────────────────────────────┘  │
│                                                                      │
│  ┌───────────────────────────────────────────────────────────────┐  │
│  │  Loaded Knowledge                                              │  │
│  │  • Mathlib4 (350K theorems)    • PhysLean (physics)           │  │
│  │  • Custom physics axioms       • @[grind]/[@simp] lemma DB   │  │
│  └───────────────────────────────────────────────────────────────┘  │
└──────────────────────────────────────────────────────────────────────┘
                            │
              ┌─────────────┴─────────────┐
              │                           │
      ┌───────▼───────┐          ┌────────▼────────┐
      │   RocksDB     │          │   PostgreSQL    │
      │  (embedded)   │          │  (TCP :5432)    │
      │               │          │                 │
      │  theorems CF  │          │  users          │
      │  proofs CF    │          │  sessions       │
      │  lineage CF   │          │  saved_searches │
      │  by_domain CF │          │  user_prefs     │
      │  by_depth CF  │          │  workers        │
      │  latex_idx CF │          │                 │
      │  stats CF     │          └────────┬────────┘
      └───────────────┘                   │
              ▲                           │
              │  POST /api/ingest         │
      ┌───────┴──────────┐               │
      │ Remote Workers   │               │
      │ (future)         │───────────────┘
      │                  │  POST /api/workers/heartbeat
      └──────────────────┘
```

**Dual Database Rationale:**
- **RocksDB** is embedded in the Rust process — zero-latency for the GA engine
  write loop and shared memory glue with Lean4. No network hop.
- **PostgreSQL** handles user-facing relational data (auth, sessions, preferences)
  and is network-accessible for distributed workers to register and heartbeat.
- The Axum API reads from both: theorem queries hit RocksDB, auth/user queries hit PostgreSQL.
- Remote workers POST verified theorems to `/api/ingest` which writes to RocksDB.
  Worker metadata (heartbeat, contribution count) goes to PostgreSQL.

---

## Component Details

### 1. Expression Representation

All mathematical expressions use a unified AST that maps cleanly between
Rust (runtime), Lean4 (verification), and the database (storage).

**Canonical Form**: Expressions are normalized before hashing:
- Variables are alpha-renamed to a canonical ordering (de Bruijn indices internally)
- Commutative operations are sorted (a + b, never b + a)
- Associative operations are flattened (a + (b + c) -> a + b + c)
- Identity elements removed (x * 1 -> x, x + 0 -> x)

**Serialization**: Protocol Buffers for RocksDB storage. Prefix notation strings
for hashing and Lean4 communication.

**Dimensional Typing**: Every expression carries a dimension type:

```rust
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Dimension {
    pub length: i8,      // L
    pub mass: i8,        // M
    pub time: i8,        // T
    pub current: i8,     // I
    pub temperature: i8, // Θ
    pub amount: i8,      // N
    pub luminosity: i8,  // J
}

impl Dimension {
    pub const ENERGY: Self = Self { length: 2, mass: 1, time: -2, ..ZERO };
    pub const FORCE: Self = Self { length: 1, mass: 1, time: -2, ..ZERO };
    pub const VELOCITY: Self = Self { length: 1, time: -1, ..ZERO };
    // ...
}
```

Any expression that produces a dimensionally inconsistent result is immediately
rejected by the GA pre-filter (before reaching Lean4).

---

### 2. Genetic Algorithm Detail

#### 2.1 Island Model

The GA uses an **island model** for parallelism:

```
┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐
│ Island 1 │     │ Island 2 │     │ Island 3 │     │ Island N │
│ Mechanics│     │   EM     │     │   QM     │     │   SR     │
│ focused  │     │ focused  │     │ focused  │     │ focused  │
└────┬─────┘     └────┬─────┘     └────┬─────┘     └────┬─────┘
     │                │                │                │
     └──── Migration every K generations ───────────────┘
            (share top theorems between islands)
```

Each island focuses on a physics domain but periodically exchanges best
theorems. This enables cross-domain discoveries (e.g., EM + SR -> relativistic
electrodynamics).

#### 2.2 Crossover Detail

**Subtree Crossover** (primary):
```
Parent A:  Apply(MP, [Axiom(F=ma), Apply(Subst, [Axiom(a=dv/dt), ...])])
Parent B:  Apply(MP, [Axiom(E_conserv), Apply(Rewrite, [Axiom(KE=mv^2/2), ...])])

Select compatible subtrees (same output type):
  From A: Apply(Subst, [Axiom(a=dv/dt), ...])
  From B: Apply(Rewrite, [Axiom(KE=mv^2/2), ...])

Child:  Apply(MP, [Axiom(F=ma), Apply(Rewrite, [Axiom(KE=mv^2/2), ...])])
```

Compatibility requires: matching types at the crossover point.

#### 2.3 Fitness Evaluation

```rust
fn evaluate_fitness(theorem: &Theorem, population: &Population, db: &DB) -> FitnessScore {
    FitnessScore {
        // 1. Novelty: semantic distance from K nearest neighbors
        novelty: novelty_score(theorem, population),

        // 2. Simplicity: prefer shorter expressions (MDL principle)
        complexity: 1.0 / (1.0 + theorem.statement.node_count() as f64),

        // 3. Derivation depth: prefer shallow (closer to axioms = more fundamental)
        depth: 1.0 / (1.0 + theorem.depth as f64),

        // 4. Dimensional consistency: 1.0 if consistent, 0.0 if not
        dimensional: if theorem.dimensions_consistent() { 1.0 } else { 0.0 },

        // 5. Symmetry: check Lorentz/gauge/rotational invariance
        symmetry: symmetry_score(theorem),

        // 6. Connectivity: how many existing theorems relate
        connectivity: db.count_connections(theorem.id) as f64 / 100.0,

        // 7. Physics relevance: pattern matching against known physics structures
        physics_relevance: physics_pattern_score(theorem),
    }
}
```

---

### 3. Database Schema

#### 3a. RocksDB (Theorem Engine)

#### Column Family: `theorems`

```
Key:   [8 bytes: xxHash64 of canonical prefix notation]
Value: TheoremRecord (protobuf)
  - id: bytes
  - statement: bytes (serialized Expr)
  - canonical_prefix: string
  - latex: string
  - domain: enum
  - depth: uint32
  - complexity: double
  - fitness: FitnessScore
  - verified: bool
  - created_at: timestamp
  - generation: uint64
```

#### Column Family: `proofs`

```
Key:   [8 bytes: theorem_id]
Value: ProofTree (protobuf)
  - Recursive tree of proof steps
  - Each step references axiom/theorem IDs
```

#### Column Family: `lineage`

```
Key:   [8 bytes: theorem_id]
Value: LineageRecord
  - parents: [theorem_id, ...]
  - children: [theorem_id, ...]
  - axiom_ancestors: [axiom_id, ...]  // transitive closure to axiom roots
```

#### Column Family: `latex_index`

```
Key:   [normalized LaTeX string]
Value: [theorem_id]
```

Normalized: whitespace removed, equivalent forms merged (e.g., `\frac{a}{b}` and `a/b`).

#### 3b. PostgreSQL (User-Facing Data)

```sql
-- Users & Auth
users (id UUID PK, email UNIQUE, password TEXT, display_name TEXT, created_at)
sessions (id UUID PK, user_id FK→users, token UNIQUE, expires_at, created_at)

-- User Data
saved_searches (id UUID PK, user_id FK→users, latex TEXT, label TEXT, created_at)
user_preferences (user_id UUID PK FK→users, preferences JSONB)

-- Distributed Workers
workers (id TEXT PK, name TEXT, host TEXT, last_seen TIMESTAMPTZ,
         theorems_contributed BIGINT, status TEXT)
```

The Axum API uses `sqlx` (async PostgreSQL driver) with compile-time query checking.

---

### 4. Lean4 FFI Bridge

#### Lean4 Side

```lean
-- Bridge/FFI.lean

/-- Initialize the Lean runtime. Must be called once from Rust. -/
@[export lean_init_runtime]
def initRuntime : IO Unit := do
  -- Load Mathlib environment
  -- Load PhysLean environment
  -- Initialize tactic state
  return ()

/-- Verify a single candidate theorem.
    Input: canonical prefix notation string
    Output: 0 = verified, 1 = rejected, 2 = timeout
    If verified, writes proof term to output buffer. -/
@[export lean_verify_candidate]
def verifyCandidate (input : @& ByteArray) (output : @& ByteArray) : IO UInt32 := do
  let stmt ← parseFromBytes input
  -- Try tactic cascade
  match ← tryVerify stmt with
  | .verified proof => writeProof output proof; return 0
  | .rejected       => return 1
  | .timeout        => return 2

/-- Simplify an expression using simp.
    Returns simplified canonical form. -/
@[export lean_simplify_expr]
def simplifyExpr (input : @& ByteArray) (output : @& ByteArray) : IO UInt32 := do
  let expr ← parseFromBytes input
  let simplified ← runSimp expr
  writeExpr output simplified
  return 0

/-- Run grind on a goal.
    Returns proof if found, timeout otherwise. -/
@[export lean_grind_goal]
def grindGoal (input : @& ByteArray) (output : @& ByteArray) : IO UInt32 := do
  let goal ← parseFromBytes input
  match ← runGrind goal (timeout := 5000) with  -- 5s timeout
  | some proof => writeProof output proof; return 0
  | none       => return 2
```

#### Rust Side

```rust
// engine/crates/lean-bridge/src/lib.rs

extern "C" {
    fn lean_init_runtime() -> i32;
    fn lean_verify_candidate(input: *const u8, input_len: usize,
                              output: *mut u8, output_cap: usize,
                              output_len: *mut usize) -> u32;
    fn lean_simplify_expr(input: *const u8, input_len: usize,
                           output: *mut u8, output_cap: usize,
                           output_len: *mut usize) -> u32;
    fn lean_grind_goal(input: *const u8, input_len: usize,
                        output: *mut u8, output_cap: usize,
                        output_len: *mut usize) -> u32;
}

pub struct LeanBridge {
    initialized: bool,
}

impl LeanBridge {
    pub fn new() -> Result<Self> {
        unsafe { lean_init_runtime(); }
        Ok(Self { initialized: true })
    }

    pub fn verify(&self, candidate: &[u8]) -> VerifyResult {
        let mut output = vec![0u8; 64 * 1024]; // 64KB output buffer
        let mut output_len: usize = 0;
        let result = unsafe {
            lean_verify_candidate(
                candidate.as_ptr(), candidate.len(),
                output.as_mut_ptr(), output.capacity(),
                &mut output_len,
            )
        };
        match result {
            0 => VerifyResult::Verified(output[..output_len].to_vec()),
            1 => VerifyResult::Rejected,
            2 => VerifyResult::Timeout,
            _ => VerifyResult::Error,
        }
    }
}
```

---

### 5. Shared Memory Protocol

For high-throughput verification, a ring buffer in shared memory:

```rust
// Shared memory layout (mmap'd file)
//
// Header (64 bytes):
//   [0..8]   write_head: AtomicU64     // Rust writes here
//   [8..16]  read_head: AtomicU64      // Lean4 reads from here
//   [16..24] result_write: AtomicU64   // Lean4 writes results here
//   [24..32] result_read: AtomicU64    // Rust reads results from here
//   [32..64] reserved
//
// Candidate Ring (N * SLOT_SIZE bytes):
//   Each slot: [4 bytes len][len bytes data][padding to SLOT_SIZE]
//
// Result Ring (N * RESULT_SIZE bytes):
//   Each slot: [1 byte status][4 bytes len][len bytes proof][padding]

const SLOT_SIZE: usize = 4096;       // 4KB per candidate
const RESULT_SIZE: usize = 65536;    // 64KB per result (proofs can be large)
const RING_SLOTS: usize = 1024;      // 1024 slots in ring
```

Rust pushes candidates into the ring. Lean4 workers pop from the ring,
verify, and push results back. Lock-free using atomic head/tail pointers.

---

### 6. Frontend Component Architecture

```
App
├── Layout
│   ├── Sidebar (navigation, domain filter)
│   └── TopBar (search trigger, stats ticker)
├── Routes
│   ├── DashboardPage
│   │   ├── StatsGrid (total theorems, rate, generation)
│   │   ├── DiscoveryFeed (SSE-driven list of new theorems)
│   │   └── DomainDistribution (chart)
│   ├── SearchPage
│   │   ├── CommandPalette (cmdk)
│   │   │   ├── LatexInput (contenteditable + KaTeX preview)
│   │   │   ├── FuzzyResults (Fuse.js matches)
│   │   │   └── ServerResults (TanStack Query)
│   │   └── ResultList
│   │       └── TheoremCard (KaTeX rendered, domain badge, depth)
│   ├── ExplorePage
│   │   ├── ReactFlowCanvas
│   │   │   ├── TheoremNode (custom node: KaTeX + domain color)
│   │   │   ├── DerivationEdge (custom edge: animated, typed)
│   │   │   └── MiniMap
│   │   ├── NodeDetail (sidebar: full proof, lineage stats)
│   │   └── FilterControls (domain, depth, complexity sliders)
│   ├── AxiomsPage
│   │   └── AxiomList (grouped by domain)
│   ├── DomainsPage
│   │   └── DomainCard (count, recent, top theorems)
│   ├── TimelinePage
│   │   └── ChronologicalList (sorted by discovery time)
│   ├── AuthPages
│   │   ├── LoginPage (email + password form)
│   │   └── RegisterPage (registration form)
│   ├── SavedSearchesPage (user's bookmarked formulas — auth required)
│   ├── SettingsPage (user preferences — auth required)
│   └── WorkerDashboardPage (active workers, contribution stats)
├── Auth
│   ├── AuthGuard (redirect to login if not authenticated)
│   └── UserMenu (avatar dropdown: saved, settings, logout)
└── Providers
    ├── QueryClientProvider (TanStack Query)
    ├── AuthProvider (session token, current user state)
    ├── SSEProvider (discovery stream)
    └── ThemeProvider
```

---

### 7. Data Flow Summary

```
1. INGEST
   Mathlib4/Metamath/PhysLean → Rust Importer → RocksDB (seed theorems)

2. GENERATE (local engine)
   RocksDB (population) → Rust GA (select, crossover, mutate) → Candidates

3. FILTER
   Candidates → Dimensional analysis → Type pre-check → Dedup → Survivors

4. VERIFY
   Survivors → Shared Memory → Lean4 Workers → Verified/Rejected

5. STORE
   Verified → RocksDB (theorem + proof + lineage) → Index updates

6. INGEST (remote workers)
   Remote Worker → POST /api/ingest → Axum dedup check → RocksDB
   Remote Worker → POST /api/workers/heartbeat → PostgreSQL

7. AUTH
   User register/login → Axum → PostgreSQL (users, sessions)
   Saved searches, preferences → Axum → PostgreSQL

8. SERVE
   Theorem queries → Axum → RocksDB → REST/SSE/WS → TanStack Start UI
   User data → Axum → PostgreSQL → REST → TanStack Start UI

9. EXPLORE
   User clicks theorem → WS request → Axum loads lineage from RocksDB
   → Graph data → React Flow renders → User expands nodes → Repeat

10. VALIDATE (academic proof export)
    User views theorem → clicks "View Proof" → Axum loads ProofTree from RocksDB
    → Renders tactic script + proof tree in detail panel
    → User clicks "Download .lean" → Axum generates standalone Lean4 file
    → File includes axiom imports, statement, and proof term
    → Academic runs `lake build` independently to re-verify
```

---

### 8. Academic Proof Validation

Every theorem in Nasrudin is formally verified by Lean4. For academics to
independently validate proofs, the system provides a complete export pipeline.

#### 8.1 Proof Storage

When Lean4 verifies a candidate, it produces a **proof term** — a Lean4
expression that witnesses the truth of the statement. This proof term is
stored alongside the theorem in RocksDB:

- **`proofs` CF**: `theorem_id → ProofRecord` containing the serialized
  proof term bytes, the tactic that succeeded, and the verification timestamp.
- **`theorems` CF**: `TheoremRecord.verified` contains `VerificationStatus::Verified`
  with the tactic name and a reference to the proof in the `proofs` CF.

#### 8.2 Proof API Endpoints

```
GET /api/theorems/:id/proof         # ProofTree JSON (structured proof steps)
GET /api/theorems/:id/proof.lean    # Standalone .lean file for independent verification
GET /api/theorems/:id/proof/tree    # Rendered proof tree (parent chain to axioms)
```

The `.lean` export endpoint generates a self-contained Lean4 file that an
academic can verify independently:

```lean
-- Auto-generated by Nasrudin
-- Theorem: energy_momentum_relation
-- Domain: SpecialRelativity
-- Depth: 8
-- Verified: 2025-03-15T14:32:01Z
-- Tactic: grind

import PhysicsGenerator.Axioms.SpecialRelativity
import PhysicsGenerator.Axioms.Mechanics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- Energy-momentum relation: E² = (pc)² + (mc²)² -/
theorem energy_momentum_relation
  (E p m : ℝ) (c : ℝ) (hc : c = speed_of_light)
  (h_rest_energy : rest_energy m c = m * c ^ 2)
  (h_momentum_energy : momentum_energy p c = p * c) :
  E ^ 2 = (p * c) ^ 2 + (m * c ^ 2) ^ 2 := by
  grind [sr_postulate_1, sr_postulate_2,
         energy_conservation, momentum_conservation]
```

To verify independently:

```bash
# Clone the Nasrudin prover project (provides axiom definitions)
git clone https://github.com/nasrudin/prover
cd prover

# Place the downloaded .lean file
cp ~/Downloads/energy_momentum_relation.lean PhysicsGenerator/Exported/

# Verify with Lake
lake build PhysicsGenerator.Exported.energy_momentum_relation
# Exit code 0 = proof checks out
```

#### 8.3 Proof Export Pipeline

```
RocksDB (proofs CF)
    │
    │  ProofTree (protobuf) + proof_term bytes
    ▼
┌─────────────────────────────────────────────────┐
│           Lean Export Generator                   │
│                                                   │
│  1. Load ProofTree from RocksDB                  │
│  2. Resolve axiom references → import statements │
│  3. Reconstruct theorem signature from Expr AST  │
│  4. Emit proof body:                             │
│     - If TacticProof: emit `by <tactic> [lemmas]`│
│     - If ProofTerm: emit term-mode proof         │
│     - If composite: emit structured proof steps  │
│  5. Add metadata header (domain, depth, date)    │
│  6. Return as UTF-8 .lean file                   │
└─────────────────────────────────────────────────┘
    │
    ▼
  GET /api/theorems/:id/proof.lean
```

The generator lives in `engine/crates/lean-bridge/src/export.rs` and handles:

- **Import resolution**: Traces the theorem's axiom ancestors and emits the
  minimal set of Lean4 imports needed.
- **Tactic reconstruction**: If Lean4 proved via `grind` or `simp`, the export
  emits the tactic call with the specific lemma set used.
- **Term-mode fallback**: If the proof was captured as a raw proof term (opaque
  bytes from Lean4), it is embedded directly.
- **Composite proofs**: For multi-step derivations (equational chains, rewrite
  sequences), the export emits a structured `calc` or `have` proof.

#### 8.4 Frontend Proof Viewer

The explore page detail panel includes a proof tab where users can:

1. **View the proof tree** — visual representation of the derivation steps
   from axioms to the theorem, showing which inference rules were applied.
2. **See the tactic script** — the Lean4 tactic that verified the theorem
   (e.g., `grind [lemma1, lemma2]`), rendered with syntax highlighting.
3. **Inspect proof metadata** — verification timestamp, tactic used,
   verification duration, Lean4 version.
4. **Download `.lean` file** — one-click export of a standalone Lean4 source
   file that can be independently verified with `lake build`.
5. **Copy proof term** — copy the raw Lean4 proof term to clipboard for use
   in other Lean4 projects.

This gives academics a complete chain of trust: browse the theorem in the UI,
inspect exactly how it was proved, download the proof, and re-verify it on
their own machine using Lean4.

---

## Distributed Worker Binary

### Overview

Nasrudin is designed as a distributed compute network. Anyone can download a
self-contained worker binary, run it, and contribute theorem generation and
verification to the network. The central server acts as the **authority**,
re-verifying every submission before accepting it.

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         Central Server                                   │
│                                                                          │
│  ┌──────────────┐  ┌────────────────┐  ┌──────────────────────────────┐ │
│  │  Axum API    │  │  Server-Side   │  │  Global RocksDB              │ │
│  │  (:3001)     │  │  Lean4 Prover  │  │  (canonical theorem store)   │ │
│  │              │  │  (re-verify)   │  │                              │ │
│  │  /api/ingest │◄─┤                │◄─┤  Only writes after server    │ │
│  │  /api/workers│  │  Validates ALL │  │  Lean4 re-verification       │ │
│  │  /api/seed   │  │  submissions   │  │  passes                     │ │
│  └──────┬───────┘  └────────────────┘  └──────────────────────────────┘ │
│         │                                                                │
│  ┌──────▼───────┐                                                        │
│  │ PostgreSQL   │  Tracks workers, contributions, user accounts          │
│  └──────────────┘                                                        │
└─────────┬───────────────────────────────────────────────────────────────┘
          │
          │  HTTPS (REST)
          │
  ┌───────┴──────────────────────────────────────────────────────┐
  │                    Public Internet                             │
  │                                                                │
  │   ┌──────────┐    ┌──────────┐    ┌──────────┐               │
  │   │ Worker 1 │    │ Worker 2 │    │ Worker N │  ...           │
  │   │ (binary) │    │ (binary) │    │ (binary) │               │
  │   └──────────┘    └──────────┘    └──────────┘               │
  └────────────────────────────────────────────────────────────────┘
```

### Worker Binary Contents

The release binary is a single executable that bundles:

| Component | Role |
|-----------|------|
| Rust GA Engine | Generates candidate theorems via genetic algorithms |
| Lean4 Prover | Formally verifies candidates locally |
| Local RocksDB | Persists local theorem state across restarts |
| HTTP Client | Communicates with the central server |

No external dependencies required. The binary is self-contained.

### Worker Lifecycle

```
┌─────────────────────────────────────────────────────────────────────┐
│  nasrudin-worker --server https://nasrudin.example.com              │
│                                                                      │
│  1. REGISTER                                                         │
│     POST /api/workers/register                                       │
│     → Server assigns worker ID, returns auth token                   │
│     → Worker stored in PostgreSQL (workers table)                    │
│                                                                      │
│  2. SEED                                                             │
│     GET /api/seed                                                    │
│     → Server returns base axiom set + recent high-value theorems     │
│     → Worker loads into local RocksDB as initial population          │
│                                                                      │
│  3. GENERATE LOOP (runs continuously)                                │
│     ┌──────────────────────────────────────────────────────────┐     │
│     │  a. Select parents from local population (NSGA-II)       │     │
│     │  b. Crossover + mutate to produce candidates             │     │
│     │  c. Pre-filter: dimensional analysis, dedup, complexity  │     │
│     │  d. Lean4 verify locally (grind, simp, omega, ...)       │     │
│     │  e. If verified → store in local RocksDB                 │     │
│     │  f. Submit to server:                                    │     │
│     │       POST /api/ingest                                   │     │
│     │       Body: { canonical, proof, lineage, domain }        │     │
│     │  g. Loop back to (a)                                     │     │
│     └──────────────────────────────────────────────────────────┘     │
│                                                                      │
│  4. HEARTBEAT (every 30s)                                            │
│     POST /api/workers/heartbeat                                      │
│     Body: { worker_id, generation, theorems_produced, uptime }       │
│     → Server updates PostgreSQL workers table                        │
│     → Server may return new seed theorems or config updates          │
│                                                                      │
│  5. SHUTDOWN                                                         │
│     Local RocksDB persists — resume where you left off               │
│     POST /api/workers/disconnect                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### Server-Side Validation Pipeline

The server does **not** trust worker submissions blindly. Every theorem
submitted via `/api/ingest` goes through a validation pipeline:

```
Worker POST /api/ingest
  │
  ▼
┌─────────────────────────────────────────────────────────┐
│ 1. DEDUP CHECK                                           │
│    Compute xxHash64 of canonical form                    │
│    Check RocksDB Bloom filter → reject if already known  │
├─────────────────────────────────────────────────────────┤
│ 2. FORMAT VALIDATION                                     │
│    Parse canonical expression string                     │
│    Verify well-formed AST                                │
│    Check dimensional consistency (SI 7-tuple)            │
├─────────────────────────────────────────────────────────┤
│ 3. COMPLEXITY BOUNDS                                     │
│    Reject trivially simple (node_count < 3)              │
│    Reject excessively complex (node_count > 10000)       │
│    Reject infinite/NaN constants                         │
├─────────────────────────────────────────────────────────┤
│ 4. SERVER-SIDE LEAN4 RE-VERIFICATION                     │
│    The server runs its own Lean4 instance                │
│    Independently verifies the proof from scratch         │
│    Does NOT trust the worker's proof — re-proves it      │
│    Timeout: 30s per theorem                              │
├─────────────────────────────────────────────────────────┤
│ 5. LINEAGE VALIDATION                                    │
│    Verify parent theorem IDs exist in global RocksDB     │
│    Verify claimed derivation path is plausible           │
├─────────────────────────────────────────────────────────┤
│ 6. ACCEPT                                                │
│    Write to global RocksDB (theorems + proofs + lineage) │
│    Update column family indexes                          │
│    Broadcast via SSE to connected frontends              │
│    Credit worker in PostgreSQL (contribution count)      │
└─────────────────────────────────────────────────────────┘
```

Steps 1-3 are fast (microseconds). Step 4 is the bottleneck — but since
workers pre-verify, the server's re-verification has a high success rate
and the proof hints from the worker accelerate the server's Lean4 pass.

### API Endpoints for Workers

| Endpoint | Method | Purpose |
|----------|--------|---------|
| `/api/workers/register` | POST | Register a new worker, receive auth token |
| `/api/workers/heartbeat` | POST | Report status, receive config updates |
| `/api/workers/disconnect` | POST | Graceful shutdown notification |
| `/api/seed` | GET | Fetch axiom set + seed theorems for initial population |
| `/api/ingest` | POST | Submit a verified theorem for server-side re-verification |
| `/api/theorems/recent` | GET | Fetch recent globally-verified theorems (worker can pull to enrich local population) |

### Worker Configuration

```bash
# Minimal: just point at the server
./nasrudin-worker --server https://nasrudin.example.com

# Full options
./nasrudin-worker \
  --server https://nasrudin.example.com \
  --threads 4 \                    # GA threads (default: num_cpus - 1)
  --data-dir ./nasrudin-data \     # Local RocksDB path (default: ./data)
  --domains mechanics,sr,em \      # Focus on specific physics domains
  --population-size 5000 \         # Per-island population (default: 10000)
  --batch-size 64 \                # Lean4 verification batch size
  --heartbeat-interval 30 \        # Seconds between heartbeats
  --name "my-worker"               # Human-readable worker name
```

### Build the Worker Binary

```bash
# Build a release binary with Lean4 prover bundled
cd engine
cargo build --release --bin nasrudin-worker

# The binary is at: target/release/nasrudin-worker
# Distribute this single file — no runtime dependencies needed
```

### Security Model

- Workers authenticate via a token received at registration
- All submissions are re-verified server-side (workers are untrusted)
- Rate limiting per worker prevents abuse
- Malformed or consistently-rejected submissions flag the worker
- The server's Lean4 instance is the single source of truth
