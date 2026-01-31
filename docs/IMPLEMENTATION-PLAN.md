# Implementation Plan: Path to Continuous Discovery

> Created: 2025-01-31
> Goal: Get the engine running on a VM, continuously discovering theorems

---

## Current State Assessment

### Working
- [x] PhysLean extraction pipeline (extract → catalog.json → generate_lean → .lean files)
- [x] Core types: Expr AST, Theorem, ProofTree, FitnessScore, Domain, Dimension
- [x] RocksDB storage: 9 column families, CRUD + indexes + stats
- [x] GA engine: crossover, mutation, selection (NSGA-II), fitness, island model (6 islands)
- [x] Lean bridge: process-based verification, tactic cascade
- [x] Derivation engine: rewrite engine, axiom store, strategies, dimension checker
- [x] Justfile: pipeline recipes, deploy infrastructure, systemd service
- [x] Generated axioms: 392 re-axiomatizable theorems across 3 domains

### Partially Working
- [x] API server: 15 endpoints wired, GA thread, verification workers, SSE stream
- [ ] Frontend: TanStack Start scaffolded, components incomplete

### Not Started
- [ ] PostgreSQL entities (SeaORM configured but empty)
- [ ] MCP server (placeholder only)
- [ ] End-to-end integration test

---

## Phase 1: Wire the Engine (Priority: CRITICAL)

The GA engine has all the pieces but they need to be connected into a working loop.

### 1.1 Axiom Loading from Catalog
**Status**: DONE
- `AxiomStore::load_from_catalog()` called at API startup in `main.rs`
- `Island::seed_from_axioms()` added — seeds GA populations with domain axioms
- `GaEngine::new()` accepts `AxiomStore` and passes to islands
- `/api/axioms` endpoint added to expose loaded axioms
- Seeding order: axioms → DB → random fill

### 1.2 GA → Lean4 Verification Loop
**Status**: DONE (was already wired in `main.rs`)
- GA thread sends candidate batches via `candidates_tx` channel
- Verification worker receives batches, calls `lean_bridge.verify_theorem()`
- Verified theorems stored in RocksDB and sent back to GA via `verified_tx`
- GA thread receives verified results and broadcasts discovery events

### 1.3 SSE Event Broadcasting
**Status**: DONE (was already wired in `main.rs`)
- `GET /api/events/discoveries` endpoint streams `DiscoveryEvent` via SSE
- GA thread broadcasts events on `discovery_tx` when theorems are verified

---

## Phase 2: API Server Endpoints (Priority: HIGH)

**Status**: DONE — all endpoints implemented in `api/src/main.rs`

### 2.1 Theorem CRUD (RocksDB) — DONE
- `GET /api/theorems/{id}` — fetch theorem by ID ✓
- `GET /api/theorems?domain=X&limit=N` — list/filter theorems ✓
- `GET /api/theorems/{id}/lineage` — derivation graph ✓
- `GET /api/theorems/{id}/proof` — proof tree ✓
- `GET /api/theorems/recent` — recent theorems ✓
- `DELETE /api/theorems/{id}` — delete theorem ✓
- `GET /api/stats` — engine statistics ✓

### 2.2 Search — DONE
- `GET /api/theorems?latex=X` — search by LaTeX prefix ✓
- `GET /api/theorems?axiom=X` — search by axiom ✓
- `GET /api/theorems?depth=N` — search by depth ✓
- `GET /api/theorems?generation=N` — search by generation ✓

### 2.3 Axiom Endpoints — DONE
- `GET /api/axioms` — list seed axioms ✓
- `GET /api/axioms?domain=X` — filter by domain ✓
- `GET /api/domains` — domain list with counts ✓
- `GET /api/ga/status` — GA engine status ✓

### 2.4 SSE Streams — DONE
- `GET /api/events/discoveries` — new theorem stream ✓
- `GET /api/events/stats` — real-time metrics (5s interval) ✓

---

## Phase 3: Integration Testing (Priority: HIGH)

### 3.1 Smoke Test
- Start engine with `just run`
- Verify axioms load from catalog
- Verify GA produces candidates
- Verify at least one candidate passes Lean4 verification
- Verify theorem stored in RocksDB
- Verify SSE stream emits the discovery

### 3.2 Pipeline Test
- `just extract-physlean` → catalog.json produced
- `just generate-axioms` → .lean files produced
- `just refresh-axioms` → prover builds
- `just run` → engine starts, GA runs, discoveries happen

---

## Phase 4: Frontend MVP (Priority: MEDIUM)

**Status**: MOSTLY DONE — pages exist and are connected to the API

### 4.1 Search Page — DONE
- Landing page with search bar and filters (domain, verification, fitness, depth) ✓
- KaTeX rendering of results ✓
- Click through to explore ✓

### 4.2 Explore Page — DONE
- React Flow canvas with theorem lineage graph ✓
- Node detail panel ✓

### 4.3 Engine Dashboard — DONE
- Live stats (SSE /api/events/stats + query polling) ✓
- Recent discoveries with TheoremCard ✓

### 4.4 Axioms Page — DONE
- Fetches from /api/axioms (was mock data, now real API) ✓
- Grouped by domain with counts ✓

### 4.5 Additional Pages — DONE
- Timeline page with live SSE discovery stream ✓
- Domain browse pages ✓
- Home page with stats and recent theorems ✓

---

## Phase 5: Hardening (Priority: LOW)

### 5.1 PostgreSQL Integration
- User auth (register/login/sessions)
- Saved searches
- Worker tracking

### 5.2 Proof Export
- `GET /api/theorems/:id/proof.lean` — standalone Lean4 file
- Proof tree viewer in frontend

### 5.3 Distributed Workers
- Ingest endpoint
- Worker registration/heartbeat
- Server-side re-verification

---

## Execution Order

### Completed
1. ~~Phase 1: Wire the Engine~~ — DONE
   - AxiomStore loaded from catalog at startup ✓
   - GA islands seeded from axioms → DB → random ✓
   - Verification loop wired via channels ✓
   - SSE broadcasting of discoveries ✓
   - Dimensional analysis pre-filter on candidates ✓
2. ~~Phase 2: API Endpoints~~ — DONE (15 endpoints + 2 SSE streams)
3. ~~Phase 4: Frontend MVP~~ — DONE (all pages connected to real API)

### Remaining
4. Phase 3: Integration testing (smoke test + pipeline test)
5. Phase 5: Hardening (PostgreSQL auth, proof export, distributed workers)
