# Physics Generator: System Plan

> Derive physics from pure logic. Bottom-up theorem generation using genetic algorithms,
> formal verification with Lean4, and an interactive exploration UI.

## 1. Vision

A system that starts from mathematical axioms and physics postulates, then uses
genetic algorithms to combine, mutate, and evolve new theorems — eventually
rediscovering known physics (like E=mc^2) without being told what to find.

**Core loop:**
```
Axioms + Inference Rules
        |
   Rust GA Engine (combine, mutate, crossover)
        |
   Candidate Theorems
        |
   Lean4 Verifier (grind, simp, type-check)
        |
   Verified Theorems --> RocksDB
        |
   UI (search, explore, visualize derivation graphs)
```

---

## 2. Knowledge Base: Getting to 1M+ Theorems

Mathlib4 contains ~350,000 theorems/definitions. To reach 1M+:

| Source | Estimated Count | Role |
|--------|----------------|------|
| Mathlib4 | ~350,000 | Pure math foundations |
| Metamath (set.mm) | ~40,000 | ZFC axiom-level proofs |
| PhysLean | ~2,000 | Formalized physics (Maxwell, QM, SR, SM) |
| Lean4PHYS/PhysLib | ~200 | Peer-reviewed physics benchmarks |
| Generated (GA output) | 600,000+ | Novel combinations and derivations |

The system seeds with existing formalized knowledge, then the GA engine
continuously generates new theorems to fill the gap beyond 1M.

---

## 3. Architecture Overview
```

### 3.2 Build Tooling

| Layer | Tool | Purpose |
|-------|------|---------|
| JS/TS | pnpm workspaces + Turborepo | Package management, cached builds |
| Rust | Cargo workspace | Crate compilation, dependency management |
| Lean4 | Lake | Lean package management, Mathlib dependency |
| Orchestration | just | Cross-ecosystem commands (`just dev`, `just build`) |

### 3.3 Type Safety Across Boundaries

```
Lean4 types (CIC) <--C ABI--> Rust types <--specta/ts-rs--> TypeScript types
```

- **Rust <-> Lean4**: C ABI structs with `#[repr(C)]`. Lean exports via `@[export]`.
  Rust declares via `extern "C"`. Reference counting handled at boundary.
- **Rust <-> TypeScript**: `specta` crate auto-generates TS types from Rust structs.
  Axum handlers return typed JSON. Frontend consumes with TanStack Query.

---

## 4. Rust Engine (`engine/`)

### 4.1 Theorem Representation

```rust
/// Canonical representation of a mathematical expression
#[derive(Clone, Hash, Eq, PartialEq)]
pub enum Expr {
    Var(Symbol),                          // x, y, m, c, E
    Const(Rational),                      // 0, 1, 2, pi
    App(Box<Expr>, Box<Expr>),            // Function application
    Lam(Symbol, Box<Type>, Box<Expr>),    // Lambda abstraction
    Pi(Symbol, Box<Type>, Box<Type>),     // Dependent function type
    Op(Operator, Vec<Expr>),              // +, *, =, ->
}

/// A theorem with its proof trace
pub struct Theorem {
    pub id: TheoremId,                    // xxHash64 of canonical form
    pub statement: Expr,                  // The proposition
    pub proof: ProofTree,                 // How it was derived
    pub depth: u32,                       // Steps from axioms
    pub complexity: f64,                  // Kolmogorov-inspired measure
    pub domain: Domain,                   // Physics domain tag
    pub parents: Vec<TheoremId>,          // What it was derived from
    pub children: Vec<TheoremId>,         // What it contributes to
    pub verified: VerificationStatus,     // Lean4 verification result
    pub fitness: FitnessScore,            // GA fitness
}

/// Proof tree tracks full derivation
pub enum ProofTree {
    Axiom(AxiomId),
    Apply(InferenceRule, Vec<ProofTree>),
    Rewrite(RewriteRule, Box<ProofTree>),
    Combine(Box<ProofTree>, Box<ProofTree>),
}
```

### 4.2 Genetic Algorithm

**Population**: Theorems stored in RocksDB. Active population held in memory (~100K).

**Genome**: `ProofTree` — a derivation tree with axiom leaves and inference-rule nodes.

**Operators**:

| Operator | Description |
|----------|-------------|
| Subtree Crossover | Swap compatible subtrees between two proof trees |
| Point Mutation | Replace an operator or rewrite rule at a random node |
| Variable Substitution | Replace a free variable with a concrete expression |
| Axiom Injection | Insert a new axiom application at a random leaf |
| Simplification | Send to Lean4 simp, replace with simplified form |
| Domain Transfer | Apply a theorem from one physics domain in another |

**Fitness Function** (multi-objective Pareto):

```rust
pub struct FitnessScore {
    pub novelty: f64,          // Distance from nearest known theorem (hash-based)
    pub complexity: f64,       // Prefer simpler expressions (Occam's razor)
    pub depth: f64,            // Prefer shallower derivations
    pub dimensional: f64,      // Dimensional analysis consistency
    pub symmetry: f64,         // Lorentz/gauge/rotational invariance score
    pub connectivity: f64,     // How many existing theorems it connects to
    pub nasrudin_relevance: f64 // Bonus for matching known physics patterns
}
```

**Selection**: NSGA-II (Non-dominated Sorting Genetic Algorithm) for multi-objective optimization.

**Key Constraints**:
- Dimensional analysis: every candidate must have consistent units
- Type safety: Lean4 type-checks every candidate before storage
- Dedup: xxHash64 of canonical prefix notation prevents duplicates

### 4.3 Engine Loop

```
┌─────────────────────────────────────────────────┐
│                  Rust GA Engine                  │
│                                                  │
│  1. Select parents from population (tournament)  │
│  2. Apply genetic operators (crossover, mutate)  │
│  3. Dimensional analysis filter (fast reject)    │
│  4. Send to Lean4 for verification               │
│  5. If verified: compute fitness, store in DB    │
│  6. If novel & high fitness: broadcast via SSE   │
│  7. Update population (NSGA-II selection)        │
│  8. Repeat                                       │
│                                                  │
│  Runs N threads, each with own population slice  │
│  Shared RocksDB for cross-thread dedup           │
└─────────────────────────────────────────────────┘
```

### 4.4 Importer Pipeline

Ingests existing theorems into RocksDB:

1. **Mathlib4**: Parse `.olean` files or use Lean4 `Environment.fold` to extract
   all declarations. Export via Lean4 FFI as serialized theorem records.
2. **Metamath**: Parse `set.mm` directly in Rust (well-defined text format).
   Map Metamath axioms to internal `Expr` representation.
3. **PhysLean** (implemented): The `physlean-extract/` project (Lean 4.16.0) walks
   PhysLean's environment and outputs `catalog.json`. The `physics-importer` crate
   (`engine/crates/importer/`) reads this catalog and:
   - Populates `AxiomStore` via `load_from_catalog()`
   - Generates `prover/PhysicsGenerator/Generated/*.lean` files (re-axiomatized
     for Lean 4.27 compatibility)
   - Pipeline: `just refresh-axioms` (extract → generate → build prover)

---

## 5. Lean4 Prover (`prover/`)

### 5.1 Role

Lean4 serves as the **verification oracle**. The Rust engine generates candidates;
Lean4 proves or rejects them.

### 5.2 Verification Pipeline

```lean
-- Bridge/Verify.lean

/-- Attempt to verify a candidate theorem.
    Returns: verified proof or error message. -/
@[export verify_candidate]
def verifyCandidate (stmt : String) : IO (Option String) := do
  -- 1. Parse the expression from canonical format
  let expr ← parseExpr stmt
  -- 2. Try automated tactics in sequence
  let result ← tryTactics expr [
    `grind,        -- SMT-style reasoning
    `simp,         -- Rewriting
    `omega,        -- Linear arithmetic
    `norm_num,     -- Numeric normalization
    `ring,         -- Ring equalities
    `linarith,     -- Linear arithmetic over ordered fields
    `field_simp,   -- Field simplification
    `polyrith,     -- Polynomial arithmetic
  ]
  return result
```

### 5.3 Custom Tactics

```lean
-- Tactics/PhysicsTactic.lean

/-- Physics-aware simplification that respects units and dimensions -/
macro "nasrudin_simp" : tactic => `(tactic|
  simp only [Units.mul_assoc, Units.inv_cancel, Dimension.consistent]
  <;> ring
  <;> norm_num)

/-- Grind with physics axioms in scope -/
macro "nasrudin_grind" : tactic => `(tactic|
  grind [lorentz_invariance, energy_conservation, momentum_conservation])
```

### 5.4 Shared Memory Architecture

Rust and Lean4 communicate via:

1. **C FFI** (primary): Lean4 exports functions, Rust calls them via `extern "C"`.
   Lean4 runtime initialized once at engine startup.
2. **Memory-mapped file** (bulk data): For large batch verification, Rust writes
   candidates to an mmap'd region. Lean4 reads from the same region.
   Avoids serialization overhead for high-throughput verification.
3. **Protocol**: Ring buffer in shared memory. Rust writes candidate at tail,
   Lean4 reads from head, writes result back to a result region.

```
┌──────────┐    mmap ring buffer    ┌──────────┐
│   Rust   │ ──── candidates ────> │  Lean4   │
│  Engine  │ <──── results ─────── │ Verifier │
└──────────┘                        └──────────┘
       │                                  │
       └────── RocksDB (verified) ────────┘
```

---

## 6. Database Layer (Dual Database)

The system uses **two databases**, each for what it does best:

| Database | Crate | Stores | Why |
|----------|-------|--------|-----|
| **RocksDB** | `engine/crates/rocks/` | Theorems, proofs, lineage, indexes | Embedded (zero-latency for engine), LSM-tree writes, built-in Bloom filters, shared memory glue between Rust and Lean4 |
| **PostgreSQL** | `engine/crates/pg/` | Users, sessions, auth, saved searches, user preferences, worker registry | Relational queries, network-accessible for distributed workers, auth primitives (pgcrypto) |

```
┌────────────────────────────────────────────────────────────┐
│                     Single Droplet                          │
│                                                             │
│  ┌──────────────────┐          ┌──────────────────┐         │
│  │    PostgreSQL     │          │     RocksDB      │         │
│  │                   │          │                   │         │
│  │  users            │          │  theorems CF      │         │
│  │  sessions         │          │  proofs CF        │         │
│  │  saved_searches   │          │  lineage CF       │         │
│  │  user_preferences │          │  by_domain CF     │         │
│  │  workers          │          │  by_depth CF      │         │
│  │                   │          │  latex_index CF   │         │
│  │                   │          │  stats CF         │         │
│  └────────┬──────────┘          └────────┬──────────┘         │
│           │                              │                    │
│  ┌────────┴──────────────────────────────┴──────────┐        │
│  │                 Axum API Server                    │        │
│  │                                                    │        │
│  │  /api/auth/*       → PostgreSQL                   │        │
│  │  /api/theorems/*   → RocksDB                      │        │
│  │  /api/ingest       → RocksDB (from remote workers)│        │
│  │  /api/events/*     → RocksDB (SSE)                │        │
│  │  /api/ws/explore   → RocksDB (WebSocket)          │        │
│  └────────────────────────┬──────────────────────────┘        │
│                           │                                    │
│  ┌────────────────────────┴──────────────────────────┐        │
│  │       Local Rust GA Engine + Lean4 Workers         │        │
│  │       (writes directly to RocksDB — embedded)      │        │
│  └────────────────────────────────────────────────────┘        │
│                                                                │
│  Remote workers POST to /api/ingest ──► Axum ──► RocksDB      │
└────────────────────────────────────────────────────────────────┘
```

### 6.1 RocksDB (Theorem Engine)

**Column Families:**

```
  "theorems"     : hash(canonical_expr) -> TheoremRecord (protobuf)
  "proofs"       : theorem_id -> ProofTree (protobuf)
  "lineage"      : theorem_id -> { parents: [id], children: [id] }
  "by_domain"    : domain:complexity:id -> theorem_id
  "by_depth"     : depth:id -> theorem_id
  "by_axiom"     : axiom_id:id -> theorem_id
  "latex_index"  : latex_normalized -> theorem_id
  "stats"        : "total_count" -> u64, "generation" -> u64, ...
```

**Deduplication:**
1. Convert to canonical prefix notation (variables alpha-renamed)
2. Compute xxHash64
3. Check Bloom filter (RocksDB built-in) — fast rejection of known theorems
4. If possibly new, check exact key lookup
5. Only store if truly novel

**Tuning:**

```rust
let mut opts = Options::default();
opts.set_write_buffer_size(128 * 1024 * 1024);      // 128MB write buffer
opts.set_max_write_buffer_number(4);                  // 4 concurrent buffers
opts.set_level_compaction_dynamic_level_bytes(true);   // Auto-tune levels
opts.set_compression_type(DBCompressionType::Lz4);     // Fast compression
opts.set_bottommost_compression_type(DBCompressionType::Zstd); // Best ratio at bottom
opts.set_bloom_locality(10);                           // Optimize bloom for SSD
```

### 6.2 PostgreSQL (User-Facing Data)

```sql
CREATE EXTENSION IF NOT EXISTS pgcrypto;

-- User accounts
CREATE TABLE users (
    id          UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    email       TEXT UNIQUE NOT NULL,
    password    TEXT NOT NULL,  -- bcrypt via pgcrypto
    display_name TEXT,
    created_at  TIMESTAMPTZ DEFAULT now()
);

-- Auth sessions
CREATE TABLE sessions (
    id          UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id     UUID REFERENCES users(id) ON DELETE CASCADE,
    token       TEXT UNIQUE NOT NULL,
    expires_at  TIMESTAMPTZ NOT NULL,
    created_at  TIMESTAMPTZ DEFAULT now()
);

-- Saved searches (user bookmarks a LaTeX formula)
CREATE TABLE saved_searches (
    id          UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id     UUID REFERENCES users(id) ON DELETE CASCADE,
    latex       TEXT NOT NULL,
    label       TEXT,
    created_at  TIMESTAMPTZ DEFAULT now()
);

-- User preferences (theme, default domain filter, etc.)
CREATE TABLE user_preferences (
    user_id     UUID PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    preferences JSONB NOT NULL DEFAULT '{}'
);

-- Registered distributed workers
CREATE TABLE workers (
    id          TEXT PRIMARY KEY,  -- worker self-assigned ID
    name        TEXT,
    host        TEXT,
    last_seen   TIMESTAMPTZ DEFAULT now(),
    theorems_contributed BIGINT DEFAULT 0,
    status      TEXT DEFAULT 'active'
);
```

### 6.3 Why Two Databases

| Concern | RocksDB | PostgreSQL |
|---------|---------|------------|
| Write throughput (1000s/sec) | Native LSM-tree | Possible but adds WAL overhead |
| Embedded (no network hop) | Yes — engine writes directly | No — always TCP |
| Bloom filter dedup | Built-in per column family | Requires application-level |
| Lean4 shared memory glue | Same process, zero-copy | Would need serialization |
| User auth (bcrypt, sessions) | No support | Native (pgcrypto) |
| Relational queries (JOINs) | No support | Native |
| Network-accessible for workers | No (embedded) | Yes (TCP) |
| Saved searches, preferences | Poor fit | Perfect fit |

The Axum API server connects to **both** — reads theorems from RocksDB, reads/writes user data in PostgreSQL. The GA engine only touches RocksDB.

---

## 7. API Server (`engine/crates/api/`)

Built with Axum. Exposes:

### 7.1 REST Endpoints — Theorems (RocksDB)

```
GET  /api/theorems/:id              # Get theorem by ID
GET  /api/theorems?q=<latex>&limit=N # Search by LaTeX expression
GET  /api/theorems/:id/lineage      # Get derivation graph (parents + children)
GET  /api/theorems/:id/proof        # Get full proof tree (JSON)
GET  /api/theorems/:id/proof.lean   # Standalone .lean file for independent verification
GET  /api/theorems/:id/proof/tree   # Rendered proof tree (parent chain to axioms)
GET  /api/stats                     # Engine statistics (count, rate, generation)
GET  /api/domains                   # List physics domains with counts
GET  /api/axioms                    # List seed axioms
POST /api/search                    # Full-text + semantic search
```

### 7.2 REST Endpoints — Auth & Users (PostgreSQL)

```
POST /api/auth/register             # Create account
POST /api/auth/login                # Login, returns session token
POST /api/auth/logout               # Invalidate session
GET  /api/auth/me                   # Current user info

GET  /api/saved-searches            # User's saved searches
POST /api/saved-searches            # Save a LaTeX search
DELETE /api/saved-searches/:id      # Remove saved search

GET  /api/preferences               # User preferences
PUT  /api/preferences               # Update preferences
```

### 7.3 REST Endpoints — Worker Ingest (RocksDB)

```
POST /api/ingest                    # Batch submit verified theorems from remote workers
POST /api/workers/register          # Register a distributed worker
POST /api/workers/heartbeat         # Worker heartbeat (updates last_seen in PostgreSQL)
GET  /api/workers                   # List active workers
```

The ingest endpoint accepts batches of verified theorems from remote workers
and writes them to RocksDB with dedup:

```rust
async fn ingest_theorems(
    State(rocks): State<RocksDb>,
    State(pg): State<PgPool>,
    Json(batch): Json<IngestBatch>,
) -> Result<Json<IngestResult>> {
    let mut inserted = 0;
    let mut duplicates = 0;

    for theorem in &batch.theorems {
        if rocks.bloom_maybe_contains(&theorem.id) {
            if rocks.theorems.get(&theorem.id)?.is_some() {
                duplicates += 1;
                continue;
            }
        }
        rocks.put_theorem(theorem)?;
        inserted += 1;
    }

    // Update worker stats in PostgreSQL
    sqlx::query("UPDATE workers SET theorems_contributed = theorems_contributed + $1, last_seen = now() WHERE id = $2")
        .bind(inserted as i64)
        .bind(&batch.worker_id)
        .execute(&pg).await?;

    Ok(Json(IngestResult { inserted, duplicates }))
}
```

### 7.4 Server-Sent Events (SSE)

```
GET /api/events/discoveries         # Stream of newly verified theorems
GET /api/events/stats               # Real-time engine metrics
GET /api/events/progress            # Generation progress updates
```

### 7.5 WebSocket

```
WS /api/ws/explore                  # Interactive graph exploration
                                    # Client sends: expand node, collapse, filter
                                    # Server sends: graph updates
```

---

## 8. Frontend (`apps/web/`)

### 8.1 Technology

| Library | Purpose |
|---------|---------|
| TanStack Start | Full-stack React framework (SSR, routing, server functions) |
| TanStack Query | Data fetching, caching, real-time sync |
| React Flow (@xyflow/react) | Node graph canvas for derivation visualization |
| KaTeX (react-katex) | LaTeX rendering in UI and graph nodes |
| cmdk | Command palette for formula search |
| Fuse.js | Client-side fuzzy search over formula index |
| Tailwind CSS | Styling |

### 8.2 Pages

| Route | Description |
|-------|-------------|
| `/` | Dashboard: live stats, generation counter, recent discoveries |
| `/search` | LaTeX autocomplete search — type formula, see matches |
| `/explore/:id` | Canvas mode: interactive derivation graph for a theorem |
| `/axioms` | Browse seed axioms and physics postulates |
| `/domains` | Browse by physics domain (mechanics, EM, QM, SR, etc.) |
| `/timeline` | Chronological discovery timeline |

### 8.3 Canvas (Explore Mode)

Interactive graph using React Flow:

- **Nodes**: Each theorem rendered with KaTeX. Color-coded by domain.
- **Edges**: Directed arrows showing derivation (parent -> child).
- **Expand**: Click a node to load its parents (what derived it) and
  children (what it contributes to).
- **Filter**: Toggle visibility by domain, complexity, depth.
- **Minimap**: Overview of the full graph.
- **Layout**: Hierarchical (dagre) with axioms at top, derived theorems flowing down.

### 8.4 Search

1. User types LaTeX in command palette (cmdk)
2. Client-side fuzzy match against cached formula index (Fuse.js)
3. Server-side search for deeper matches (POST /api/search)
4. Results show: rendered formula + domain + depth + match score
5. Click result to open in Canvas explore mode

### 8.5 Real-Time Updates

```typescript
// Subscribe to discovery stream
const eventSource = new EventSource('/api/events/discoveries');
eventSource.onmessage = (event) => {
  const theorem = JSON.parse(event.data);
  queryClient.setQueryData(['theorems', theorem.id], theorem);
  // Toast notification for significant discoveries
  if (theorem.fitness.nasrudin_relevance > 0.8) {
    toast(`New discovery: ${theorem.latex}`);
  }
};
```

---

## 9. Physics Axioms (Seed Knowledge)

### 9.1 Mathematical Foundations

Start from ZFC set theory axioms (via Mathlib4):
- Extensionality, Pairing, Union, Power Set, Infinity, Replacement, Regularity, Choice

Plus core mathematical structures:
- Real numbers (complete ordered field)
- Vector spaces, inner product spaces
- Differential calculus, integration
- Group theory, Lie groups

### 9.2 Physics Postulates (from PhysLean)

All physics axioms are sourced from **PhysLean**, a formally verified physics library.
No hand-coded axioms. See [PHYSICS-AXIOMS.md](./PHYSICS-AXIOMS.md) for full details.

| Domain | PhysLean Coverage | Key Theorems |
|--------|------------------|--------------|
| Classical Mechanics | Strong | Euler-Lagrange, Hamilton's equations, Noether's theorem, harmonic oscillator |
| Special Relativity | Very Strong | Lorentz group (SL(2,C)), Pauli matrices, mass-shell, twin paradox, time dilation |
| Electromagnetism | Strong | Maxwell field tensor, EM potential (F=dA), plane waves, gauge invariance |
| Quantum Mechanics | Moderate | Harmonic oscillator (E_n = ℏω(n+½)), creation/annihilation commutation |
| Thermodynamics | Shallow | Ideal gas law (PV=nRT), Boltzmann distribution |
| General Relativity | **Absent** | No coverage — domain is empty until PhysLean adds it |

Domains grow automatically as PhysLean adds coverage. Re-run `just refresh-axioms`
to pick up new theorems.

### 9.3 Inference Rules

The GA combines axioms using:

| Rule | Description |
|------|-------------|
| Modus Ponens | From `P` and `P -> Q`, derive `Q` |
| Universal Instantiation | From `forall x, P(x)`, derive `P(a)` |
| Substitution | Replace variable with expression |
| Equational Reasoning | From `a = b`, derive `f(a) = f(b)` |
| Rewriting | Apply simp lemmas to simplify |
| Dimensional Composition | Combine dimensionally compatible expressions |
| Algebraic Manipulation | Ring/field operations on equations |
| Limit/Approximation | Take limits, Taylor expand |

---

## 10. Deriving E=mc^2 (Example Path)

The system does NOT know E=mc^2. It has:
- SR postulate 1: speed of light `c` is constant
- SR postulate 2: laws are Lorentz invariant
- Conservation of energy
- Conservation of momentum
- Mathematical tools (calculus, algebra, group theory)

**Expected GA derivation path** (simplified):

```
Step 1:  SR postulates → Lorentz transformation (via grind on the two postulates)
Step 2:  Lorentz transform + conservation laws → 4-momentum is conserved
Step 3:  4-momentum definition → E^2 = (pc)^2 + (mc^2)^2  (energy-momentum relation)
Step 4:  Set p=0 (rest frame) → E = mc^2
```

Each step is a theorem in the database. The GA discovers intermediate steps
by combining axioms. Lean4 verifies each step. The fitness function rewards:
- Dimensional consistency (energy = mass * velocity^2)
- Lorentz invariance
- Novel combinations of known theorems
- Connections to multiple domains

---

## 11. Implementation Phases

### Phase 1: Foundation
- [ ] Set up monorepo (pnpm + Cargo + Lake)
- [ ] Define `Expr`, `Theorem`, `ProofTree` types in Rust
- [ ] Set up RocksDB with column families (`engine/crates/rocks/`)
- [ ] Set up PostgreSQL with user/auth tables (`engine/crates/pg/`)
- [ ] Create Lean4 project with Mathlib dependency
- [ ] Build C FFI bridge (Lean4 exports, Rust imports)
- [ ] Implement basic verification: Rust sends expr string, Lean4 returns verified/rejected

### Phase 2: Knowledge Ingestion
- [ ] Mathlib4 theorem extractor (via Lean4 Environment.fold)
- [ ] Metamath set.mm parser in Rust
- [x] PhysLean importer (`physlean-extract/` + `engine/crates/importer/`)
- [x] Physics axiom formalization in Lean4 (auto-generated from PhysLean catalog)
- [ ] Populate RocksDB with seed knowledge
- [ ] Build dedup pipeline (canonical form + xxHash64)

### Phase 3: Genetic Algorithm
- [ ] Implement NSGA-II selection
- [ ] Subtree crossover operator
- [ ] Point mutation operator
- [ ] Variable substitution operator
- [ ] Dimensional analysis filter
- [ ] Fitness function (multi-objective)
- [ ] Multi-threaded engine loop
- [ ] Shared memory ring buffer for Lean4 verification

### Phase 4: API Server
- [ ] Axum REST endpoints — theorems, search, lineage, stats (from RocksDB)
- [ ] Axum REST endpoints — auth, register, login, sessions (from PostgreSQL)
- [ ] Proof endpoints — proof tree JSON, standalone .lean export, proof tree rendering
- [ ] Lean export generator (ProofTree → standalone .lean file with imports)
- [ ] Ingest endpoint for remote worker theorem submission
- [ ] Worker registration and heartbeat endpoints
- [ ] SSE event streams (discoveries, stats, progress)
- [ ] WebSocket for interactive graph exploration
- [ ] TypeScript type generation via specta

### Phase 5: Frontend
- [ ] TanStack Start project setup
- [ ] Dashboard with live stats
- [ ] LaTeX search with KaTeX rendering + cmdk + Fuse.js
- [ ] React Flow canvas for derivation graph exploration
- [ ] Domain browser
- [ ] Timeline view
- [ ] Proof viewer in explore detail panel (tactic display, proof tree, metadata)
- [ ] Download .lean button (calls GET /api/theorems/:id/proof.lean)
- [ ] Copy proof term button

### Phase 6: LLM Integration
- [ ] Tactic advisor: LLM predicts which Lean4 tactic to try first (5x verification speedup)
- [ ] LLM-guided crossover: FunSearch pattern — LLM suggests combinations instead of random
- [ ] MCP server (`physics-generator-mcp`) exposing theorem DB, GA engine, Lean4 as tools
- [ ] Curator loop: LLM periodically reviews theorem DB, adjusts exploration weights
- [ ] Graceful degradation: system runs pure GA when LLM is unavailable

See [LLM-INTEGRATION.md](./LLM-INTEGRATION.md) for full architecture.

### Phase 7: Optimization & Scale
- [ ] Profile and optimize GA throughput
- [ ] Parallel Lean4 verification workers
- [ ] RocksDB compaction tuning
- [ ] Incremental graph loading for large derivation trees
- [ ] Formula embedding search (semantic similarity)
- [ ] Distributed worker mode: remote Rust+Lean4 workers POST to /api/ingest
- [ ] Worker Bloom filter sync (periodic pull from central RocksDB)
- [ ] PostgreSQL connection pooling for many concurrent workers

---

## 12. Key Technical Risks

| Risk | Mitigation |
|------|------------|
| Lean4 FFI is C-only, no first-class Rust support | Use lean-sys crate + handwritten C ABI wrappers. Existing RustCallLean project proves feasibility |
| Lean4 verification is slow per-theorem | Batch verification, multiple Lean4 processes, pre-filter with dimensional analysis |
| GA search space is astronomically large | Constrain with dimensional analysis, type checking, domain tagging. Use fitness to prune aggressively |
| E=mc^2 derivation may take very long | The system runs continuously. Success is measured by coverage of known physics, not speed |
| Mathlib4 extraction is non-trivial | PhysLean project has solved this. Reuse their approach |
| 1M+ theorems may overwhelm RocksDB | RocksDB handles 500M+ keys in production at Meta. Not a concern |
| Two databases adds operational complexity | PostgreSQL only stores user data (small, low-write). RocksDB is embedded (no ops). Single droplet keeps both local |
| Distributed workers need dedup coordination | Workers maintain local Bloom filters + central RocksDB dedup via /api/ingest with ON CONFLICT-style idempotency |

---

## 13. Success Criteria

1. **Seed**: 350K+ Mathlib theorems + physics axioms loaded and queryable
2. **Generate**: Engine produces >1000 verified theorems/hour
3. **Rediscover**: System derives at least one known physics result (e.g., Lorentz
   transformation, harmonic oscillator solution, or E=mc^2)
4. **Explore**: User can search any LaTeX formula and see its derivation graph
5. **Scale**: Database reaches 1M+ verified theorems
6. **Type Safe**: Full end-to-end type safety from Lean4 through Rust to TypeScript
7. **Validate**: Any theorem's proof is downloadable as a standalone `.lean` file
   that an academic can independently verify with `lake build` — no trust in the
   server required
