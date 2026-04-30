# Nasrudin

**Derive physics from pure logic.** Nasrudin discovers theorems by generating candidates and formally proving them in Lean 4. A distributed theorem generation engine that starts from mathematical axioms and physics postulates, then uses genetic algorithms to evolve new theorems -- eventually rediscovering known physics (like E=mc^2) without being told what to find. Synthetic theorem generation with formal verification.

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

## Platform features

The web UI and API server share a single auth model:

- **Cookie sessions** for the web UI (axum-login + tower-sessions, Argon2 passwords).
- **Bearer API keys** (`Authorization: Bearer nsk_live_…`) for programmatic clients.

Both flow through the same `AuthOrApiKey` extractor and resolve to the same user.
Worker registration uses a separate `nsk_worker_…` key issued at registration time.

Generate keys at `/api-keys` once you're signed in.

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

Workers also pull a fresh `SteeringConfig` (see below) from `/api/seed` on every chunk boundary so the LLM-driven steerer can re-bias the entire fleet's exploration without requiring a worker restart.

**Download a release binary** and you're contributing compute to the network. No setup beyond running the executable.

## LLM-Driven Cluster Steering

A naïve genetic algorithm running across thousands of volunteer workers is unfocused: it grinds through the entire axiom space with no notion of what the corpus actually needs next. Nasrudin solves this by having an LLM **steer the cluster** every 10 minutes.

```
   Aggregate user demand            Last 10 cycles' outcomes
   (saved searches, paid hunches,   (theorems verified, domain split,
    active conjecture jobs)          cascade rejects, lake fail rate)
                  \                 /
                   \               /
                    v             v
            ┌────────────────────────────┐
            │  DigitalOcean Gradient     │
            │  Kimi K2.5 (kimi-k2.5)
            │  POST /v1/chat/completions │
            └────────────┬───────────────┘
                         │
                  SteeringConfig JSON
                  (domain weights, axiom emphasis,
                   mutation knobs, soft + hard targets)
                         │
                         v
              ArcSwap snapshot in API
                         │
        ┌────────────────┼────────────────┐
        │                │                │
   /api/steering    /api/seed (folded)  workers fold + bias
   (ETag/304)       on every poll       next chunk's GA run
```

The steerer runs in two modes:

- **Mode C — full authority.** When no paid Researcher jobs are running, Kimi has full control: it sets `domain_weights` (a probability simplex over physics domains), `axiom_emphasis` (per-axiom multiplicative bias), `fitness_weights` (novelty / dimensional elegance / chain-length penalty / target proximity), and `mutation_knobs` (rate, suffix bias, population size, elitism fraction). It can also inject `soft_targets` and `hard_targets` to point the explorer fleet at specific lemmas.

- **Mode B — knobs locked.** As soon as ≥1 paid conjecture job is `claimed` or `running`, the steerer flips to mode B: it can still re-balance domain weights and emphasis, but `mutation_knobs` are forced `null` and `hard_targets` are emptied. This keeps the slot-hour accounting paid customers are billed against predictable; the steerer's job in mode B is to bias the *explorer fleet* toward prerequisite lemmas in the active-job domains, not to retune the GA out from under a running paid slice.

Each cycle's *outcome* (theorems verified, actual domain distribution, cascade rejects, lake failure rate, manual verifies) is captured and fed back into the next cycle's prompt — so the steerer learns from what actually happened, not just what it asked for.

**Validation & safety.** Every emitted `SteeringConfig` is range-checked (domain weights sum to 1, mutation rate ∈ [0.05, 0.30], population size ∈ [32, 512], etc.). On any failure — Gradient outage, parse error, validator reject — the daemon transparently falls back to the last-known-good config and flags the row in `cluster_steering`. The cluster keeps running with stale-but-validated steering indefinitely.

The Gradient API key (`GRADIENT_API_KEY`) is server-owned and lives only in the daemon's environment. It is never exposed to clients and is distinct from the per-user encrypted-key flow used by the FunSearch-style conjecture creator.

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
├── nasrudin-frontend/       # TanStack Start v1 web UI (React 19, TS, Biome)
│   └── src/
│       ├── routes/          # /, /browse, /theorem/$id, /signin, /profile,
│       │                    # /api-keys, /api-docs, /leaderboard, /pricing
│       ├── components/      # platform shell, landing, browse, theorem, auth, apikeys
│       ├── lib/             # apiFetch, queries, types, katex helper
│       └── styles/          # tokens.css, styles.css, platform.css
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
# Connect to the Nasrudin network. By default the worker contributes
# to paid-Researcher compute alongside background research — the
# platform is sustained by paying customers, so spare capacity helps
# pay the bills.
./nasrudin-worker --server https://nasrudin.org

# Background research only (skip paid jobs):
./nasrudin-worker --server https://nasrudin.org --no-paid-jobs

# Legacy LLM-guided FunSearch flow:
./nasrudin-worker --server https://nasrudin.org --research-mode
```

The worker binary bundles the Rust GA engine and Lean4 prover. It runs locally on your machine, generates and verifies theorems, and submits discoveries to the central server. Your local RocksDB persists across restarts so no work is lost.

The 96 slot-hour quota per paid job and the cluster's 10 % explorer floor mean a vanilla worker still spends the bulk of its compute on background research even with paid-jobs enabled — paid claims are gated server-side so they can never starve the explorer fleet.

**What workers do each chunk** (a chunk is a few generations of GA, roughly 30–60 s):

1. **Try a paid claim first** (default; suppress with `--no-paid-jobs`). POST `/api/jobs/claim` with the worker's currently-available lake slots. On award, hand the entire chunk to the paid-slice runner — it heartbeats every 30 s with deltas (candidates attempted, candidates verified, slot-hours consumed) and on a kernel-verified theorem calls `/api/jobs/{id}/mark_proved`.
2. **Otherwise**, sync from `/api/seed`: pull any new peer-verified theorems into the local AxiomStore, refresh the `rejected_canonicals` memo (so we skip lake-builds the cluster has already failed), and read the current `SteeringConfig`.
3. **Run a chunk of GA** under the active config and submit kernel-verified discoveries to `/api/ingest`.

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
| **Cluster Steerer** | Kimi K2.5 via DigitalOcean Gradient | `kimi-k2.5` |

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

## Paid Researcher Tier

The $19/mo Researcher tier turns Nasrudin into a **research assistant**: hand the system a specific conjecture you can't prove, and a slice of the GA cluster will try to evolve a Lean 4 proof of that statement for up to 24 hours.

```
User submits hunch ──> POST /api/research/jobs (one credit debited atomically)
                              │
                              v
                       conjecture_jobs row queued
                       (96 lake-slot-hour quota,
                        4 slots × 24 h)
                              │
              workers polling /api/jobs/claim with FOR UPDATE SKIP LOCKED
                              │
                              v
                       Paid GA slice runs on N worker(s)
                              │
                       heartbeat every 30 s ──> /api/jobs/{id}/heartbeat
                       (server clamps slot-hour delta at
                        2 × wallclock × slots_held to defeat
                        a worker that lies about its progress)
                              │
                ┌─────────────┴────────────┐
                │                          │
       kernel-verified theorem      budget exhausted (96h reached)
                │                          │
                v                          v
       POST /api/jobs/{id}/mark_proved   release; SSE BudgetExhausted
       state='proved'                   state='budget_exhausted'
```

**Capacity policy.** Every paid job has a hard cap of **96 lake-slot-hours** (4 slots × 24 h). The cluster always reserves at least 10 % of total worker slots (or a minimum of 2) for the explorer fleet — the claim path runs `floor_satisfied(total, paid + new_claim)` before awarding any job, so paid load can never starve background research. Excess paid jobs queue on `slice_priority DESC, created_at ASC` until capacity frees up.

**Refund rule.** A credit is refunded only if the run produced **zero verified results AND fewer than 1000 candidates attempted** (the user's hunch genuinely got no traction). Anything past those thresholds is "value delivered" — partial chains are published as ChainVerified theorems under the user's attribution and the credit stays consumed.

**Live progress.** Every paid job has a per-job SSE stream at `/api/research/jobs/{id}/events` carrying `Progress`, `TheoremVerified`, `Proved`, `BudgetExhausted`, and `Cancelled` events. The user's dashboard subscribes once when they open a job and watches it run live.

**Resilience.** Each claim grants a 5-minute lease, refreshed by every heartbeat. If a worker dies mid-grind the lease falls into the past and the reaper task (running every 60 s) requeues the job — another worker picks it up within seconds, no human intervention.

The Researcher tier also includes 10K API requests/day and unlimited corpus access. Submit a paid conjecture from the [Pricing](https://nasrudin.org/pricing) page once you're signed in.

## Support

The corpus is open by principle and built by volunteer worker compute. What it costs us to run — central Lean4 re-verification, the embedding index, hosting, ingest, the engineering time that keeps all of it improving — is funded by sponsorships.

If Nasrudin is useful to you, sponsor it: **https://nasrudin.org/sponsor** (Stripe-hosted, $5/mo and up; one-time gifts also welcome).

Sponsorship is a donation, not a subscription tier — it doesn't grant Researcher quota. If you need targeted GA compute pointed at your own conjecture, see the **Paid Researcher Tier** section above and the [Pricing](https://nasrudin.org/pricing) page.

## License

AGPL-3.0. See [`LICENSE`](./LICENSE).

The platform has a SaaS component (`api.nasrudin.org`) — the network-use clause means anyone running modified versions as a hosted service must publish their changes.

## Cutting a worker release

All cross-platform worker binaries are built locally on macOS via `just`; we do not use GitHub Actions for release builds.

```bash
# release-worker requires a clean tree — stash any in-flight work first:
git stash push -u -m "pre-release-WIP"

# Cut the release. Cross-compiles the worker binary for Linux x86_64/aarch64,
# macOS x86_64/arm64, and Windows x86_64 locally via cargo-zigbuild, then
# uploads everything to a GitHub release.
just release-worker v0.1.0

# Pop your in-flight work:
git stash pop
```

Prerequisites: `zig` and `cargo-zigbuild` installed (`brew install zig && cargo install cargo-zigbuild`); `gh auth status` shows write access to `Nasdin/nasrudin`. The recipe will add any missing rustup targets automatically.
