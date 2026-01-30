# Nasrudin

**Derive physics from pure logic.** Nasrudin discovers theorems by generating candidates and formally proving them in Lean4A distributed theorem generation engine that starts from mathematical axioms and physics postulates, then uses genetic algorithms to evolve new theorems -- eventually rediscovering known physics (like E=mc^2) without being told what to find. Synthetic theorem generation with formal verification

Named after [Nasrudin](https://en.wikipedia.org/wiki/Nasreddin), the wise fool of Sufi tradition who found truth through unconventional paths.

## How It Works

```
Mathematical Axioms (350K+ from Mathlib) + Physics Postulates (~43 axioms)
        |
   Rust GA Engine (combine, mutate, crossover expressions)
        |
   Candidate Theorems
        |
   Lean4 Formal Verifier (grind, simp, omega, ring, ...)
        |
   Verified Theorems --> RocksDB
        |
   Server re-verifies --> Accepted into global theorem database
```

Nasrudin doesn't know what physics looks like. It generates candidate mathematical statements by combining and mutating existing theorems, then uses Lean4 to formally prove or reject them. Over time, the system builds up a corpus of verified mathematical truths -- some of which turn out to be real physics.

Every theorem carries its full Lean4 proof. Academics can inspect proofs in the web UI, download any theorem as a standalone `.lean` file, and independently re-verify it with `lake build` -- no trust in the server required.

## VISION: Distributed Architecture

Nasrudin is designed as a **distributed compute network**. Anyone can contribute by running a worker node:

```
                    ┌──────────────────────┐
                    │   Central Server     │
                    │                      │
                    │  Axum API (:3001)    │
                    │  RocksDB (theorems)  │
                    │  PostgreSQL (users)  │
                    │  Lean4 (re-verify)   │
                    └──────────┬───────────┘
                               │
              POST /api/ingest │  (verified theorems)
              POST /api/workers/heartbeat
                               │
          ┌────────────────────┼────────────────────┐
          │                    │                    │
   ┌──────▼──────┐     ┌──────▼──────┐     ┌──────▼──────┐
   │  Worker 1   │     │  Worker 2   │     │  Worker N   │
   │  (home PC)  │     │  (cloud)    │     │  (your PC)  │
   │             │     │             │     │             │
   │  Rust GA    │     │  Rust GA    │     │  Rust GA    │
   │  Lean4      │     │  Lean4      │     │  Lean4      │
   │  RocksDB    │     │  RocksDB    │     │  RocksDB    │
   │  (local)    │     │  (local)    │     │  (local)    │
   └─────────────┘     └─────────────┘     └─────────────┘
```

**Workers** run the full Rust engine + Lean4 prover locally. They generate and verify theorems independently, then POST discoveries to the central server. The server performs a **second round of verification** with its own Lean4 instance before accepting theorems into the global database. This double-verification prevents invalid or malicious submissions.

**Download a release binary** and you're contributing compute to the network. No setup beyond running the executable.

## Project Structure

```
nasrudin/
├── engine/                  # Rust workspace (7 crates)
│   ├── crates/
│   │   ├── core/            # Expr AST, Dimension types, Theorem, xxHash IDs
│   │   ├── rocks/           # RocksDB embedded theorem store (9 column families)
│   │   ├── pg/              # SeaORM 2 PostgreSQL (users, auth, workers)
│   │   ├── lean-bridge/     # C ABI FFI bridge to Lean4 prover
│   │   ├── api/             # Axum HTTP server (REST + SSE + WebSocket)
│   │   ├── mcp/             # MCP server for LLM-guided exploration
│   │   └── importer/        # Mathlib/Metamath/PhysLean ingestion
│   └── Cargo.toml           # Workspace root
├── prover/                  # Lean4 formal verification
│   ├── PhysicsGenerator/
│   │   ├── Axioms/          # Formalized physics (mechanics, SR, EM, QM, thermo)
│   │   └── Bridge/          # FFI exports (pg_init, pg_verify, pg_shutdown)
│   ├── lakefile.lean
│   └── lean-toolchain       # Lean4 v4.27.0
├── nasrudin-frontend/       # TanStack Start web UI
│   └── src/
│       ├── routes/          # Dashboard, search, explore canvas, axioms, timeline
│       └── components/      # TheoremCard, DomainBadge, Sidebar
├── docs/                    # Design documents
│   ├── PLAN.md              # Master plan
│   ├── ARCHITECTURE.md      # System diagrams
│   ├── DATA-MODEL.md        # Type definitions (Rust + TypeScript)
│   ├── PHYSICS-AXIOMS.md    # All 43 physics axioms formalized
│   ├── LEAN4-BRIDGE.md      # FFI specification
│   ├── FRONTEND.md          # UI architecture
│   └── LLM-INTEGRATION.md  # MCP + LLM-guided exploration
├── justfile                 # Cross-ecosystem task runner
└── pnpm-workspace.yaml      # Monorepo config
```

## Getting Started

### Prerequisites

- **Rust** 1.92+ (`curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh`)
- **Lean4** v4.27.0 (`curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh`)
- **Node.js** 22+ and **pnpm** 9+ (`corepack enable && corepack prepare pnpm@latest --activate`)
- **PostgreSQL** 18 (for user accounts -- workers don't need this)
- **Docker** (optional, for easy PostgreSQL setup)

### Run the Server

```bash
# 1. Start PostgreSQL
just db-start

# 2. Build and run the Rust engine + API server
just dev-engine
# -> Axum API on http://localhost:3001

# 3. Start the frontend
just dev-frontend
# -> TanStack Start on http://localhost:3000
```

### Run as a Worker

Download the latest release binary for your platform, then:

```bash
# Connect to the Nasrudin network and start generating theorems
./nasrudin-worker --server https://nasrudin.org
```

The worker binary bundles the Rust GA engine and Lean4 prover. It runs locally on your machine, generates and verifies theorems, and submits discoveries to the central server. Your local RocksDB persists across restarts so no work is lost.

### Build Everything

```bash
just build           # Build frontend + engine + prover
just test            # Run all tests
just check           # Lint and typecheck
just clean           # Remove all build artifacts
```

## Tech Stack

| Layer | Technology | Version |
|-------|-----------|---------|
| **GA Engine** | Rust | 2024 edition |
| **Formal Prover** | Lean4 + Mathlib | v4.27.0 |
| **Theorem Store** | RocksDB (embedded) | 0.24 |
| **User Database** | PostgreSQL + SeaORM 2 | 18 / 2.0.0-rc |
| **API Server** | Axum | 0.8 |
| **Frontend** | TanStack Start + React 19 | v1 |
| **Math Rendering** | KaTeX | 0.16 |
| **Graph Canvas** | React Flow | 12 |
| **LLM Integration** | MCP (Model Context Protocol) | -- |

## The GA Engine

The genetic algorithm evolves mathematical expressions using an **island model** where each island focuses on a physics domain (mechanics, electromagnetism, quantum mechanics, special relativity, thermodynamics, general relativity).

**Selection**: NSGA-II multi-objective optimization balancing proof depth, novelty, dimensional correctness, and domain coverage.

**Crossover**: Subtree exchange between two parent expressions, guided optionally by LLM suggestions (FunSearch pattern).

**Pre-filters** reject candidates before they reach Lean4:
- Dimensional analysis (SI 7-tuple type system)
- Deduplication (xxHash64 + Bloom filter)
- Complexity bounds (max AST node count)
- Fast type checking

Only candidates that pass all pre-filters are sent to Lean4 for formal verification.

## Dual Database Design

| Database | Purpose | Access Pattern |
|----------|---------|----------------|
| **RocksDB** | Theorems, proofs, lineage graphs, indexes | Embedded in Rust process -- zero-latency for the GA write loop |
| **PostgreSQL** | Users, sessions, saved searches, worker metadata | Network-accessible for distributed workers and the web UI |

Workers maintain their own local RocksDB. When a worker discovers a verified theorem, it POSTs to the server's `/api/ingest` endpoint. The server re-verifies with its own Lean4 instance and, if valid, adds the theorem to the global RocksDB.

## Contributing Compute

Nasrudin is designed so anyone can contribute. When you run a worker:

1. The binary starts the Rust GA engine and Lean4 prover on your machine
2. It fetches the current axiom set and seed theorems from the server
3. Your machine generates candidate theorems via genetic algorithms
4. Lean4 formally verifies each candidate locally
5. Verified theorems are submitted to the central server
6. The server re-verifies before accepting (double verification)
7. Your contribution is tracked and attributed

All theorem generation and verification happens on your hardware. The server only receives pre-verified results and confirms them.

## License

MIT
