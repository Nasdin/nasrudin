# Phase 9 — Distributed Theorem Platform: Persistent, API-Served, DigitalOcean-Deployed

**Status:** Design approved, awaiting implementation plan.
**Authors:** Nasrudin + Claude.
**Date:** 2026-04-28.

## Goal

Move the verified-theorem corpus off ad-hoc files in `prover/PhysicsGenerator/Derived/` and into a redeploy-safe storage layer behind a public API, so:

- Verified theorems persist across `git pull && docker compose up -d` redeploys.
- Verified theorems persist across droplet rebuilds and (with up to 1 h loss) catastrophic failure.
- Future remote workers can hydrate from the API and contribute back through the same ingest endpoint as the in-process worker.
- The frontend at `nasrudin.org` browses and downloads `.lean` proofs from the live corpus.
- The system is deployable to a single DigitalOcean droplet and one config-translation step away from DigitalOcean App Platform.

E=mc² discovery acceleration is **not** a Phase 9 goal — that work continues independently in `crates/ga`. Phase 9 is purely the persistence + serving + ingest infrastructure.

## Non-goals

The following items from `docs/PLAN.md` and `docs/ARCHITECTURE.md` are explicitly deferred to **Phase 10 (public worker binary release + hostile-worker hardening)** rather than silently dropped:

- **Lineage-validity verification** — ARCHITECTURE step-5 ("server verifies parent IDs exist + claimed derivation path is plausible") is deferred. Phase 9 stores `parents`/`children` for provenance display only; it does not reject submissions whose claimed parents don't exist server-side. Acceptable while ingest is in-process; mandatory once external workers can submit.
- **Self-service worker key issuance** — `nsk_worker_*` keys are issued via `docker compose run … issue-worker-key` CLI in Phase 9. A registration UI + revocation list ships in Phase 10.
- **WebSocket `/api/ws/explore`** for interactive graph expansion (PLAN 7.5) — defer.
- **MCP server** (`crates/mcp`) for LLM-guided exploration — defer; ARCHITECTURE peer-component status acknowledged but not built in Phase 9.
- **Importer crate** (`crates/importer`) — not touched in Phase 9.
- **Auto-scaling** — single droplet, vertical scale only. Horizontal scaling is by way of users running their own worker binary in Phase 10+.

Out of scope without future phase association:

- Multi-worker leaderboards beyond a simple `verified_count` + `theorems_contributed` per worker.

## Architecture

```
                          Internet
                              |
                              v
                   ┌──────────────────────┐
                   │  Cloudflare (proxy)  │  edge TLS, DDoS, caching
                   └──────────┬───────────┘
                              | HTTPS (origin pull)
                              v
   ┌──────────────────────────────────────────────────────────┐
   │                    DigitalOcean droplet                  │
   │                    (single VM, vertical scale)           │
   │                                                          │
   │   Caddy :443/:80                                         │
   │     nasrudin.org    → :3000  (frontend, landing+platform)│
   │     api.nasrudin.org→ :3001  (Axum API)                  │
   │     origin.nasrudin.org → :3001  (CF-grey emergency)     │
   │                                                          │
   │   Frontend  :3000   ──fetch+SSE──►  Axum API  :3001      │
   │                                       │ │ │              │
   │                       ┌───────────────┘ │ └──────┐       │
   │                       v                 v        v       │
   │                  Postgres           RocksDB  Reverify    │
   │                  (SeaORM 2)         (9 CFs)  Queue       │
   │                       │                 │     │          │
   │                       │                 │     v          │
   │                       │                 │  Lake Builder  │
   │                       │                 │  pool (tokio)  │
   │                       │                 │                │
   │                       └────/data/────────                │
   │                       (block volume mount)               │
   │                                                          │
   │   GA Worker (separate container, profile: workers)       │
   │     POST /api/ingest over loopback HTTPS                 │
   │     bearer: nsk_worker_*                                 │
   │                                                          │
   │   Backup container (every 1h)                            │
   │     pg_dump + rclone /data → DO Spaces                   │
   │                                                          │
   └──────────────────────────────────────────────────────────┘

                              │ (Phase 10)
                              v
                   ┌────────────────────────────────────┐
                   │ Remote workers                     │ download nasrudin-worker
                   │ POST /api/ingest                   │ same contract as in-proc
                   │ GET  /api/seed                     │ axiom catalog + seed theorems
                   │ GET  /api/theorems                 │ paginated hydrate
                   │ SSE  /api/events/discoveries       │ live theorem feed
                   │ SSE  /api/events/stats             │ live GA tick stream
                   │ POST /api/workers/heartbeat        │ liveness + counters
                   └────────────────────────────────────┘
```

### Topology decisions (locked)

| Decision | Choice | Rationale |
|---|---|---|
| Hosting | One DigitalOcean droplet | Vertical-scale only; horizontal via user-run remote workers in Phase 10 |
| Edge | Cloudflare orange-cloud | Free DDoS, edge caching, edge TLS |
| TLS at origin | Caddy auto-LE | Box safe to expose if CF fails; emergency `origin.nasrudin.org` grey-cloud bypass |
| Domain | `nasrudin.org` (apex = frontend), `api.nasrudin.org` (API) | Frontend is landing+platform combined; remote workers point at stable `api.*` |
| Storage | Block volume mounted at `/data`, hourly Spaces backup | Redeploy-safe, droplet-rebuild-safe, ≤1 h loss tolerance |
| Postgres | Self-hosted in container on `/data/postgres` | Cost; trivially swap to Managed Postgres later via env var |
| Process model | docker-compose, all services containerized | Portable to App Platform without rewrite |
| Scheduling | tokio in-process for in-band work; backup container with internal cron loop | systemd-free, App-Platform-portable |

### Component runtime model

| Component | Runtime | Phase 9 droplet | Future App Platform |
|---|---|---|---|
| Postgres | Container | docker-compose service, `/data/postgres` mount | DO Managed Postgres (env-var change) |
| Caddy | Container | docker-compose service, ports 80+443 | replaced by App Platform edge ingress |
| Frontend | Container | docker-compose service `:3000` | App Platform Service component |
| Axum API | Container | docker-compose service `:3001` | App Platform Service component |
| GA Worker | Container | docker-compose service, profile `workers` | App Platform Worker component |
| Lake Builder | tokio task pool inside API | inside API container | inside API container |
| Reverify Queue drain | tokio task inside API | inside API container | inside API container |
| Backup job | Container with internal cron loop | docker-compose service | App Platform Job with cron schedule |

## Components

### Reused as-is

- `crates/core` — `Expr`, `Theorem`, `ProofTree`, `TheoremId`, `Domain`, `FitnessScore`, `Dimension`. No changes.
- `crates/rocks` — `TheoremDb` with 9 existing column families (theorems, proofs, lineage, by_domain, by_depth, by_axiom, by_generation, latex_index, stats). Phase 9 adds **one new column family**: `reverify_queue` (key = job id, value = serialised `ReverifyJob{theorem_id, attempts, enqueued_at}`). Persisting the queue in RocksDB means in-flight jobs survive API restarts; the drain task scans this CF on boot and resumes work. Also adds boot-time hydration of theorem CFs from Postgres if empty.
- `crates/derive` — `AxiomStore`, `Chain`, `RuleStep`, `lean_emitter`. Used by the A-path regen step in the Reverify Queue. No structural changes.
- `crates/pg` — SeaORM 2 setup, existing entities (users, sessions, api_keys, workers, saved_searches, user_preferences). Migration framework already in place.

### Existing API endpoints (kept as-is, no Phase 9 changes)

These already exist in `crates/api/src/handlers/` and are called by `nasrudin-frontend/src/lib/queries.ts`. Phase 9 must **not** break them:

| Endpoint | Handler | Frontend caller |
|---|---|---|
| `GET /api/auth/me` · `POST /api/auth/{login,register,logout}` | `me.rs`, `auth.rs` | `useMe`, `useLogin`, `useRegister`, `useLogout` |
| `GET /api/api-keys` · `POST /api/api-keys` · `DELETE /api/api-keys/:id` | `api_keys.rs` | `useApiKeys`, `useCreateApiKey`, `useDeleteApiKey` |
| `POST /api/workers/register` | `workers.rs` | (worker bootstrap) |
| `GET /api/saved-searches` · CRUD | `saved_searches.rs` | `useSavedSearches`, mutations |
| `GET /api/preferences` · `PATCH /api/preferences` | `preferences.rs` | `usePreferences` |

### Existing API endpoints (extended in Phase 9)

| Endpoint | What changes | Frontend caller |
|---|---|---|
| `GET /api/me/stats` | new query against new `theorems` table for the user's contributor counts | `useMeStats` (profile menu) |
| `GET /api/workers` | new list endpoint over existing `pg::workers` entity, returns `{worker_id, handle, host, theorems_contributed, last_seen, status}[]` | `useWorkers` (leaderboard) |
| `GET /api/domains` | enumerate `Domain` enum + per-domain count from RocksDB stats CF | (browse sidebar filter) |
| `GET /api/axioms` · `GET /api/axioms?domain=X` | exposes `AxiomStore` catalog (existing in-memory) over HTTP | (theorem detail page, future remote-worker seed) |

### New or substantially changed in Phase 9

| Component | What's new |
|---|---|
| `crates/api/src/handlers/ingest.rs` | New. `POST /api/ingest` accepts `IngestBatch{worker_id, theorems[]}`. |
| `crates/api/src/handlers/theorems.rs` | New. `GET /api/theorems` (filterable + cursor-paginated), `GET /api/theorems/recent`, `GET /api/theorems/:id`, `GET /api/theorems/:hash/lean`. |
| `crates/api/src/handlers/events.rs` | New. `GET /api/events/discoveries` and `GET /api/events/stats` — preserves existing two-stream SSE convention from PLAN/ARCHITECTURE. |
| `crates/api/src/handlers/seed.rs` | New. `GET /api/seed?domain=X` returns axiom catalog + top-N high-fitness theorems for remote-worker bootstrap. |
| `crates/api/src/handlers/workers.rs` | Extended with `POST /api/workers/heartbeat` and `GET /api/workers` (list). |
| `crates/api/src/reverify.rs` | New. Queue drain, A→B fallback verification, status transitions, contributor counter increment. |
| `crates/api/src/lake_builder.rs` | New. Tokio task pool that runs `lake build` in tmpdir copies of `prover/`. Pre-flight strips/rejects submissions containing `axiom` or `sorry` declarations. |
| `crates/api/src/hydration.rs` | New. Boot-time RocksDB hydration from Postgres. |
| `crates/api/src/rate_limit.rs` | Extended. Add per-worker token-bucket on `contributor_id` (existing module already has IP-based limiter scaffolding). |
| `crates/pg` migrator | New migration: `theorems` table (full column list — see "Postgres theorems schema" below). |
| `crates/pg/src/query/theorems.rs` | New. Insert (with same-tx contributor counter increment), dedup-by-hash, status update, list-with-cursor, by-contributor query. |
| `crates/pg/src/query/workers.rs` | Extended. Add `list_all`, `update_heartbeat`, `increment_contribution`. |
| `crates/ga/src/bin/discover_emc2.rs` | Modified. Replace file-write path with HTTP POST to `/api/ingest` as a batch of one. |
| `crates/api/src/bin/backfill_existing_lean.rs` | New. One-time script: walks `prover/PhysicsGenerator/Derived/*.lean`, submits each through the ingest pipeline as if a worker had submitted, leaves files in place. |
| `nasrudin-frontend/src/lib/queries.ts` | Extended. Add `useDiscoveryFeed()` and `useStatsStream()` hooks reading the existing `/api/events/{discoveries,stats}` paths. Existing `useRecentTheorems`/`useTheorem` need only server-side endpoints to be implemented to match. |
| `deploy/docker-compose.yml` | New. Replaces existing systemd unit. |
| `deploy/Caddyfile` | New. |
| `deploy/scripts/bootstrap.sh` | New. Idempotent fresh-droplet setup. |
| `deploy/scripts/restore-from-spaces.sh` | New. Disaster recovery. |
| `docs/RUNBOOK.md` | New. Operations playbook. |
| `docs/DEPLOYMENT.md` | New. Deploy guide. |

### Boundary contracts

- **API ↔ Reverify Queue.** API may only enqueue. Only the Reverify Queue may write `Verified` or `Rejected` status. Single auditable transition path.
- **GA Worker ↔ API.** HTTP only, even on loopback. No shared memory, no shared DB handles. The GA worker is the v1 stress test for the remote-worker contract.
- **API ↔ RocksDB.** Read-heavy from API handlers. Writes only from the Reverify Queue and the boot-time hydration path. No write contention.
- **API ↔ Postgres.** `theorems` table is append-only after acceptance; updates only flip `Pending → Verified/Rejected`. Other tables are full CRUD.

## Wire format

`POST /api/ingest`. Authentication via `Authorization: Bearer nsk_worker_*`. Submissions are **batched** (matches PLAN.md and ARCHITECTURE.md `IngestBatch` contract) — a single worker discovery is just a one-element array. Batching amortises HTTP overhead for remote workers and lets the server hold one transaction window for related theorems.

```json
{
  "worker_id": "in-proc-worker-1",
  "engine_git_sha": "cffe109",
  "lean_version": "4.27.0",
  "theorems": [
    {
      "canonical_statement": "E = m * c^2",
      "latex": "E = mc^2",
      "domain": "SpecialRelativity",
      "lean_source": "import PhysicsGenerator.Axioms\n\ntheorem rest_energy ...\n  := by ...",
      "chain": [
        {"type": "IntroduceAxiom", "axiom_name": "four_momentum_time_component"},
        {"type": "IntroduceAxiom", "axiom_name": "minkowski_invariant_def"},
        {"type": "IntroduceAxiom", "axiom_name": "invariant_mass_postulate"},
        {"type": "IntroduceAxiom", "axiom_name": "rest_frame_psq_zero"},
        {"type": "RearrangeEquation", "target": "...", "description": "..."},
        {"type": "TakePositiveRoot"}
      ],
      "axioms_used": ["four_momentum_time_component", "minkowski_invariant_def", "invariant_mass_postulate", "rest_frame_psq_zero", "c_positive", "mass_nonneg", "energy_nonneg"],
      "parents": ["<hex theorem_id>", "<hex theorem_id>"],
      "origin": {"type": "Crossover", "parent_a": "<hex>", "parent_b": "<hex>"},
      "depth": 6,
      "complexity": 12,
      "generation": 24,
      "fitness": {"novelty": 0.91, "depth": 0.5, "dimensional_correctness": 1.0, "domain_coverage": 0.4, "compactness": 0.7, "axiom_efficiency": 0.6, "nasrudin_relevance": 0.8},
      "verification_tactic": "nlinarith",
      "verification_duration_ms": 47213,
      "dimension": [1, 2, -2, 0, 0, 0, 0]
    }
  ]
}
```

Required fields per theorem: `canonical_statement`, `lean_source`, `domain`, `chain`, `axioms_used`. Optional but strongly preferred: `parents`, `origin`, `fitness`, `latex`, `depth`, `generation`, `verification_tactic`, `verification_duration_ms`, `dimension`. Optional fields are nullable in Postgres and don't fail validation; they enable SQL filtering, leaderboard ranking, and graph rendering.

**Response shapes:**

- `202 Accepted` on full or partial accept:
  ```json
  {
    "results": [
      {"theorem_id": "<hex>", "canonical_hash": "<hex>", "status": "Pending"},
      {"theorem_id": "<hex>", "canonical_hash": "<hex>", "status": "Duplicate", "existing_status": "Verified"}
    ]
  }
  ```
  One result per submitted theorem, in the same order. `Duplicate` short-circuits the queue and returns the existing record's status.

- `400 Bad Request` if the entire batch is malformed (auth/schema/size).
- `429 Too Many Requests` if the worker exceeds its per-worker rate limit (`X-RateLimit-Reset` header indicates retry time).
- `503 Service Unavailable` if global queue depth exceeds 200 (with `Retry-After` header).

## Trust model — A-first, B-fallback hybrid

Two phases: synchronous validation in the ingest handler, then asynchronous verification on dequeue.

**Synchronous (ingest handler, cheap, < 50 ms per theorem in batch):**
1. Bearer-key authentication; resolve to `worker_id`.
2. Per-worker rate limit (token bucket on `worker_id`, default 60 theorems/min, configurable per-key in Postgres).
3. Schema + size validation per theorem.
4. **Lean source pre-flight** (cheap regex/parse): reject the theorem with `400 Bad Request{reason: "axiom_or_sorry_in_source"}` if the submitted `lean_source` declares a new `axiom` or contains a `sorry` placeholder. This is the firewall against trivially false submissions — a hostile worker can no longer slip a theorem through B-path by axiomatizing the conclusion. Standard Mathlib `axiom` declarations from imports are fine since they're not in the *submitted* source.
5. **Dedup**: `canonical_hash(canonical_statement)` against Postgres `theorems`. If found, return `Duplicate` result for that theorem — no enqueue, no insert.
6. INSERT theorem with `status = Pending`, attribute `contributor_id = worker_id`. Broadcast `theorem_pending` on `/api/events/discoveries`.
7. Enqueue `{theorem_id, attempts: 0}` into the `reverify_queue` CF.
8. Return `202 Accepted` with one result per submitted theorem.

**Asynchronous (Reverify Queue drain, slow, ≤ 300 s per job):**
1. **A-path (optimistic)**: regenerate Lean from `chain` via the server's own `AxiomStore` + `lean_emitter`. Run `lake build`. If it compiles AND the proven theorem matches `canonical_statement` → **accept**, store regenerated Lean as canonical, mark `Verified`.
2. **B-path (fallback)**: if A failed for any reason — unknown `RuleStep` variant, regen Lean doesn't compile, regen theorem mismatches `canonical_statement` — run `lake build` on the worker-submitted `lean_source` (already pre-flighted free of `axiom`/`sorry`). If it compiles AND it proves `canonical_statement` → **accept**, store worker's Lean as canonical, mark `Verified`, log `server_emitter_drift{engine_git_sha=...}`.
3. **Same-transaction side effects on accept:** in the same Postgres transaction that flips `Pending → Verified`, also `UPDATE workers SET theorems_contributed = theorems_contributed + 1, last_contribution_at = NOW() WHERE id = contributor_id`. Leaderboard reads see the increment atomically with the verification.
4. **Reject** with `Rejected{reason}` if both fail. Status flip is broadcast on `/api/events/discoveries`. No contributor counter increment on reject.

By the time the queue drain runs, dedup and pre-flight have already happened — the row in Postgres carries the canonical hash and is known to be free of `axiom`/`sorry`.

**Why hybrid:** the artifact the network is collecting is a *theorem* — `(statement, lean-proof, axioms-used)`. The chain is the GA's path; two different chains can yield the same theorem. Once the Lean source compiles in Lean 4 + Mathlib AND contains no fresh axioms or `sorry`s, the math is real. A-first regeneration adds provenance validation when versions align; B-fallback ensures forward-compatibility across engine versions; pre-flight ensures B-fallback is genuine independent verification, not just compile-checking trusted-worker output.

**Phase 9 trust caveat:** the in-process worker is fully trusted (same machine, same engine SHA). The full hostile-remote-worker hardening — lineage validation, parent-existence checks, axiom-set whitelist enforcement, version-min negotiation — is documented in non-goals as deferred to Phase 10. Phase 9's pre-flight + dedup gives sufficient protection for Phase 9's threat model (one in-process worker, no external network).

## Postgres `theorems` schema

The `theorems` table mirrors enough of the RocksDB `Theorem` record that SQL queries can drive leaderboards, contributor stats, fitness-filtered browse, and remote-worker hydration without round-tripping through RocksDB. Columns:

| Column | Type | Source | Indexed |
|---|---|---|---|
| `id` | `BYTEA` (8 bytes, xxHash64) | `theorem_id` | PRIMARY KEY |
| `canonical_hash` | `BYTEA` (8 bytes) | hash of normalised `canonical_statement` | UNIQUE |
| `canonical_statement` | `TEXT` | wire format | — |
| `latex` | `TEXT` | wire format (nullable) | — |
| `lean_source` | `TEXT` | accepted Lean (regen on A, submitted on B) | — |
| `domain` | `TEXT` | wire format | btree |
| `axioms_used` | `TEXT[]` | wire format | gin |
| `chain_json` | `JSONB` | wire format `chain` | — |
| `parents` | `BYTEA[]` | wire format (nullable) | gin |
| `origin_kind` | `TEXT` | `"Axiom"` / `"Crossover"` / `"DomainTransfer"` / `"Mutation"` | — |
| `origin_payload` | `JSONB` | tagged-union body for `Crossover{a,b}`, etc. | — |
| `depth` | `INT` | wire format (nullable) | btree |
| `complexity` | `INT` | wire format (nullable) | — |
| `generation` | `BIGINT` | wire format (nullable) | btree |
| `fitness_novelty` | `REAL` | wire format `fitness.novelty` | — |
| `fitness_compactness` | `REAL` | wire format | — |
| `fitness_dimensional_correctness` | `REAL` | wire format | — |
| `fitness_domain_coverage` | `REAL` | wire format | — |
| `fitness_axiom_efficiency` | `REAL` | wire format | — |
| `fitness_nasrudin_relevance` | `REAL` | wire format | — |
| `fitness_depth_score` | `REAL` | wire format `fitness.depth` | — |
| `dimension` | `INT[7]` | wire format SI 7-tuple (nullable) | — |
| `engine_git_sha` | `TEXT` | wire format batch header | — |
| `lean_version` | `TEXT` | wire format batch header | — |
| `verification_tactic` | `TEXT` | filled by Reverify Queue on `Verified` | — |
| `verification_duration_ms` | `INT` | filled by Reverify Queue | — |
| `verification_path` | `TEXT` | `"A"` or `"B"` (which path accepted) | — |
| `status` | `TEXT` | `"Pending"` / `"Verified"` / `"Rejected"` | btree |
| `rejected_reason` | `TEXT` | nullable | — |
| `contributor_id` | `BYTEA` | FK → `workers.id` | btree |
| `created_at` | `TIMESTAMPTZ` | server-set | btree |
| `verified_at` | `TIMESTAMPTZ` | nullable | — |

**Cursor for pagination:** the API's cursor is `(verified_at, id)` — a stable, monotonic compound key. Cursor format on the wire: `base64url(verified_at_micros || id_bytes)`. The `total` field returned alongside results is a fast `COUNT(*)` over the same filter, capped at 10 000 for safety (`total_capped: bool`).

**Workers table extension:** `workers` adds `theorems_contributed BIGINT DEFAULT 0`, `last_contribution_at TIMESTAMPTZ`, `last_heartbeat_at TIMESTAMPTZ`, `current_generation BIGINT`, `theorems_produced_total BIGINT`, `uptime_seconds BIGINT`. All set/incremented by ingest and heartbeat handlers.

## Data flow

### Ingest

```
GA Worker            Axum API                       Reverify Queue       Lake Builder         Postgres + RocksDB                    SSE clients
    │                    │                                │                    │                       │                                  │
    ├── POST /api/ingest ►                                │                    │                       │                                  │
    │   {worker_id,      │                                │                    │                       │                                  │
    │    theorems[N]}    │                                │                    │                       │                                  │
    │                    ├── verify bearer + rate-limit ──────────────────────────────────────────────►│                                  │
    │                    │   per worker_id                │                    │                       │                                  │
    │                    │                                │                    │                       │                                  │
    │                    │ for each submitted theorem:    │                    │                       │                                  │
    │                    ├── pre-flight: reject if axiom/sorry in lean_source                          │                                  │
    │                    ├── canonical_hash dedup ─────────────────────────────────────────────────────►│                                 │
    │                    ├── INSERT theorem(Pending,     │                    │                        │                                  │
    │                    │   contributor=worker_id) ───────────────────────────────────────────────────►│                                 │
    │                    │                                │                    │                       ├── theorem_pending ───────────────►│
    │   202 Accepted ◄───┤                                │                    │                       │                                  │
    │   {results[N]}     │                                │                    │                       │                                  │
    │                    ├── enqueue ─────────────────────►                    │                       │                                  │
    │                    │                                ├── A-path: regen ───►                       │                                  │
    │                    │                                │                    ├── lake build (~60s) ──┤                                  │
    │                    │                                │ if A passes (same tx):                     │                                  │
    │                    │                                │   UPDATE Verified, store regen_lean ──────►│                                  │
    │                    │                                │   UPDATE workers SET theorems_contributed += 1                                 │
    │                    │                                │                    │                       ├── theorem_verified ──────────────►│
    │                    │                                │ if A fails: B ─────►                       │                                  │
    │                    │                                │                    ├── lake build ─────────┤                                  │
    │                    │                                │ if B passes (same tx):                     │                                  │
    │                    │                                │   UPDATE Verified, store worker_lean,      │                                  │
    │                    │                                │   log server_emitter_drift                 │                                  │
    │                    │                                │   UPDATE workers SET theorems_contributed += 1                                 │
    │                    │                                │                    │                       ├── theorem_verified ──────────────►│
    │                    │                                │ if both fail:                              │                                  │
    │                    │                                │   UPDATE Rejected{reason}                  │                                  │
    │                    │                                │   no contributor increment                 │                                  │
    │                    │                                │                    │                       ├── theorem_rejected ──────────────►│
```

### Boot / hydration

API connects Postgres → runs migrations → opens RocksDB → counts theorems in RocksDB. If empty, `SELECT * FROM theorems WHERE status='Verified'`, `TheoremDb::put_theorem` for each row, then `API ready`. Idempotent — restartable mid-hydration.

### Read

Frontend SSR hits `GET /api/theorems?domain=sr&limit=50` and `GET /api/theorems/recent?limit=50` — both already wired in `nasrudin-frontend/src/routes/browse.tsx`. Server reads RocksDB hot path for indexed queries; falls back to Postgres for SQL-only filters (e.g. by_contributor, leaderboard). Hash-to-id mapping lives in Postgres because `canonical_hash` is a Postgres-natural lookup. `.lean` download endpoint reads `proof.lean_source` from RocksDB.

### SSE — two streams (preserves existing convention)

`/api/events/discoveries` and `/api/events/stats` are kept as two distinct streams per ARCHITECTURE.md and PLAN.md. The existing `discovery_tx: broadcast::Sender<DiscoveryEvent>` in `state.rs` becomes the source for both — events are filtered per-stream.

| Stream | Path | Events | Frontend hook |
|---|---|---|---|
| Discoveries | `GET /api/events/discoveries` | `theorem_pending{theorem_id, canonical, contributor_id}`, `theorem_verified{theorem_id, verification_path, duration_ms}`, `theorem_rejected{theorem_id, reason}` | `useDiscoveryFeed()` invalidates `['theorems', ...]` on each event |
| Stats | `GET /api/events/stats` | `ga_status_tick{generation, candidates_evaluated, queue_depth}`, `worker_heartbeat{worker_id, theorems_produced_total, current_generation}` | `useStatsStream()` updates dashboard widgets |

Both streams send a keep-alive comment line every 15 s. Cloudflare must have a Page Rule on these paths setting cache=bypass and buffering=off (already noted in DNS/Cloudflare section).

### Heartbeat

`POST /api/workers/heartbeat`. Authentication via `nsk_worker_*`. Body matches ARCHITECTURE spec:

```json
{
  "worker_id": "in-proc-worker-1",
  "current_generation": 24,
  "theorems_produced_total": 1283,
  "uptime_seconds": 7341,
  "engine_git_sha": "cffe109"
}
```

Server `UPDATE workers SET last_heartbeat_at = NOW(), current_generation = $2, theorems_produced_total = $3, uptime_seconds = $4, status = 'Active' WHERE id = $1`. Broadcasts a `worker_heartbeat` event on `/api/events/stats`. Workers ping every 30 s; the API marks `status = 'Stale'` on workers whose `last_heartbeat_at` is older than 5 min (background tokio task, scans hourly).

### Backup

Backup container, every 1 h:
1. `pg_dump --format=custom postgres > /tmp/pg.dump`
2. `rclone sync /data/rocks/ spaces:nasrudin-backups/$(date +%Y/%m/%d/%H)/rocks/`
3. `rclone copy /tmp/pg.dump spaces:nasrudin-backups/$(date +%Y/%m/%d/%H)/postgres.dump`
4. Delete dumps older than 30 days on Spaces.

Restore: pull latest dir from Spaces to `/data`, `pg_restore`, `docker compose up -d`.

### Future remote-worker sync (Phase 10, sketch only)

Same `POST /api/ingest` contract. Cold start: `GET /api/seed?domain=X` for axiom catalog + top-N high-fitness seed theorems → `GET /api/theorems?since=<cursor>&limit=1000` paginated full hydrate → `GET /api/events/discoveries` for live deltas → optional `GET /api/events/stats` for cluster-wide GA telemetry. No code path is special-cased for "remote".

## Existing `prover/PhysicsGenerator/Derived/` files policy

The `prover/PhysicsGenerator/Derived/` tree currently contains:

- **Hand-authored canonical proofs**: `RestEnergyUpstream.lean`, `PhotonEnergyMomentum.lean`. These are committed reference proofs and the user's "no cheating" milestones. **Keep committed**, untouched.
- **Auto-emitted deterministic proofs**: `AutoRestEnergyUpstream.lean`. Produced by the `derive_emc2_upstream` binary. **Keep committed**, regeneratable on demand from the deterministic strategy.
- **GA-discovered files**: `DiscoverGen{n}.lean` from prior iterations 12–24. Several are real verified discoveries (`(c·p0)² = E²`, `Msq = m²·c²`, etc.); spec acceptance criterion 8 forbids the GA from writing these going forward.

**Phase 9 transition plan:**

1. **Backfill script** (`crates/api/src/bin/backfill_existing_lean.rs`, run once at deploy time): walks every `.lean` file in `prover/PhysicsGenerator/Derived/`, extracts the canonical statement (parsed from the `theorem name (...) : <statement> := by ...` skeleton), reconstructs a synthetic chain (single-step `IntroduceAxiom` for hand proofs; loaded from a sidecar JSON for `Discover*.lean` if available, else single-step `External` provenance), and submits the batch through the production `/api/ingest`. The backfill worker uses a special `nsk_worker_backfill` key so its submissions are tagged distinctly in the leaderboard.
2. **Files stay on disk** as the canonical reference for academic reproducibility — `lake build` against the committed tree is still expected to succeed end-to-end.
3. **Going forward** (acceptance criterion 8): `crates/ga/src/bin/discover_emc2.rs` writes no new `Discover*.lean` files; it POSTs verified discoveries through the API. The Reverify Queue's accepted Lean source lives in Postgres + RocksDB only.

This way the existing milestones are preserved AND visible in `/browse` after deploy, AND the GA worker is forced through the ingest pipeline as the sole production-time write path.

## Failure modes

### Ingest validation
| Failure | HTTP | Response |
|---|---|---|
| Missing/malformed bearer | 401 | reject batch |
| Non-worker key prefix | 403 | reject batch |
| Per-worker rate limit exceeded | 429 | reject batch with `X-RateLimit-Reset` header |
| Global queue depth > 200 | 503 | reject batch with `Retry-After` header |
| Batch schema invalid | 400 | reject batch with field-level error |
| Theorem `lean_source` contains fresh `axiom` or `sorry` | per-theorem result `Rejected{axiom_or_sorry_in_source}` | other theorems in batch proceed |
| `canonical_hash` already in Postgres | per-theorem result `Duplicate{existing_status}` | other theorems in batch proceed |
| `lean_source` > 256 KiB | per-theorem result `Rejected{too_large}` | — |
| `chain` > 64 steps | per-theorem result `Rejected{too_complex}` | — |
| `worker_id` not registered or revoked | 403 | reject batch |
| `engine_git_sha` below `MIN_SUPPORTED_ENGINE_SHA` env var | 426 Upgrade Required | reject batch with `X-Required-Engine-SHA` header |

### Reverify queue
| Failure | Response |
|---|---|
| Lake builder process crashes | tmpdir cleaned by `Drop`, job re-enqueued up to 3 attempts, then `Rejected{ToolchainError}` |
| Lake build > 300 s | kill subprocess, `Rejected{VerifyTimeout}` |
| A-path regen fails, B passes | accept B, log `server_emitter_drift` |
| A-path passes with different theorem than claim | `Rejected{ChainMismatch}` |
| Both paths fail | `Rejected{reason}` with stderr tail |
| Queue depth > 200 | API returns 429 on `/api/ingest` until depth < 100 |

### Storage consistency
| Scenario | Response |
|---|---|
| Postgres commit ok, RocksDB write fails | log `rocks_write_lag`, reconcile on next hydration sweep, reads fall back to Postgres |
| RocksDB ok, Postgres fails | impossible by ordering (Postgres always commits first) |
| RocksDB corruption at boot | rename `/data/rocks/` to `.corrupt.<ts>/`, full hydrate from Postgres, alert |
| Postgres unreachable at boot | API enters degraded mode: refuses ingest (503), serves reads from RocksDB, frontend shows read-only banner |

### Background tasks
| Task | Failure | Response |
|---|---|---|
| Reverify drain | tokio panic | supervised by `JoinSet`; restart with exponential backoff |
| SSE keep-alive | client drops | broadcast handles via `Lagged`, slow clients dropped, others unaffected |
| Backup container | `pg_dump` fails | retry once, then alert; never block API |
| Backup container | Spaces unreachable | accumulate locally up to 24 h, alert at 6 h |

### GA worker
| Failure | Response |
|---|---|
| Container OOM | `restart: unless-stopped`; loses unverified candidates only |
| Worker key revoked | API responds 401, container exits non-zero, no auto-restart loop |
| API unreachable | exponential backoff up to 5 min; queue verified-but-not-submitted in worker's local RocksDB; flush on reconnect |

### Capacity
| Resource | Threshold | Response |
|---|---|---|
| `/data` disk | 85% | reject ingest with 507; auto-prune `/data/lake-cache/` |
| Postgres connections | pool exhausted | API returns 503; pool size 16 |
| Lake builder slots | all 2 busy | enqueue normally — queue is the buffer |
| RAM | OOM | container restart; persistent state survives because nothing in-flight bypasses the queue |

### Drift observability
Every B-path acceptance is a signal. Aggregate per `engine_git_sha`:
- `> 5%` of ingests hitting B → bump worker binary release.
- `> 50%` → mandatory worker upgrade banner on `/api-keys` page.
- Rejected-with-`ChainMismatch` from a known-good worker SHA → server emitter regression alarm.

### Single load-bearing invariant

**Postgres is always at least as fresh as RocksDB.** Every other failure mode reduces to "re-derive RocksDB from Postgres".

## Deployment

### Resources

| Resource | DO product | Sizing | Cost/mo |
|---|---|---|---|
| Droplet | Premium Intel, regular SSD | `s-4vcpu-8gb` | $48 |
| Block volume | DO Block Storage | 50 GB SSD | $5 |
| Spaces bucket | DO Spaces | `nasrudin-backups`, 250 GB included | $5 |
| DNS | Cloudflare free tier | apex + `api` + `origin` | $0 |
| Domain | `nasrudin.org` | Namecheap or DO registrar | ~$1 |
| **Total** | | | **~$60/mo** |

8 GB RAM floor: Postgres ~512 MB + RocksDB cache ~1 GB + 2× Lake builders (~2.5 GB peak each) + Axum ~200 MB + Caddy ~50 MB + frontend SSR ~300 MB + headroom. Migrate to `s-8vcpu-16gb` (~$96/mo) when sustained queue depth > 50 indicates the lake-builder pool needs widening.

### New files

```
deploy/
  docker-compose.yml          ← replaces existing systemd unit
  Caddyfile
  .env.example
  rclone.conf.example
  scripts/
    bootstrap.sh
    restore-from-spaces.sh
docs/
  RUNBOOK.md
  DEPLOYMENT.md
```

`deploy/physics-generator.service` is **deleted**. `deploy/cron-refresh.sh` is rewritten as a service in `docker-compose.yml`.

### docker-compose.yml shape

```yaml
services:
  postgres:           # mount /data/postgres
  caddy:              # ports 80, 443; volume for cert state
  api:                # build engine/, depends on postgres
  frontend:           # build nasrudin-frontend/, runs node SSR
  ga-worker:          # profile: workers, env API_URL=http://api:3001
  backup:             # internal cron loop, mounts /data + rclone.conf

volumes:
  data:               # bind from /mnt/nasrudin-data (block volume)
```

### Caddyfile

```
nasrudin.org {
  reverse_proxy frontend:3000
  encode zstd gzip
}

api.nasrudin.org {
  reverse_proxy api:3001
  header Access-Control-Allow-Origin "https://nasrudin.org"
}

origin.nasrudin.org {
  reverse_proxy api:3001
}
```

### Environment

Single `/opt/nasrudin/.env` (mode 0600), documented in `.env.example`:

```
POSTGRES_PASSWORD=<gen>
NASRUDIN_INTERNAL_WORKER_KEY=<gen, nsk_worker_*>
NASRUDIN_API_PUBLIC_URL=https://api.nasrudin.org
NASRUDIN_FRONTEND_PUBLIC_URL=https://nasrudin.org
RCLONE_CONFIG=/etc/rclone.conf
DO_SPACES_BUCKET=nasrudin-backups
SESSION_SECRET=<gen>
ARGON2_PEPPER=<gen>
```

`bootstrap.sh` generates `<gen>` values on first run, idempotent on re-run.

### DNS / Cloudflare (one-time, manual)

1. Register `nasrudin.org`, point nameservers at Cloudflare.
2. Records:
   - `nasrudin.org` → A → droplet IP, **proxied (orange cloud)**
   - `api.nasrudin.org` → A → droplet IP, **proxied**
   - `origin.nasrudin.org` → A → droplet IP, **DNS-only (grey cloud)** — emergency bypass
3. SSL/TLS mode: **Full (strict)** (Caddy presents valid LE cert at origin).
4. Page Rules: `api.nasrudin.org/api/events/*` → cache=bypass, buffering=off (Cloudflare buffers SSE by default and will break the streams).

### Bootstrap (fresh droplet)

```
1. doctl compute droplet create … --user-data deploy/scripts/bootstrap.sh
2. doctl compute volume-action attach <vol-id> <droplet-id>
3. ssh in, mount volume at /mnt/nasrudin-data
4. cd /opt/nasrudin (cloned by bootstrap.sh)
5. cp .env.example .env && edit secrets
6. docker compose pull && docker compose up -d
7. docker compose run --rm api /usr/local/bin/migrate                # SeaORM migrations
8. docker compose run --rm api /usr/local/bin/backfill_existing_lean # one-shot, ingests prover/Derived/*.lean
9. open https://nasrudin.org → landing renders, /browse shows backfilled theorems
10. docker compose run --rm api /usr/local/bin/issue-worker-key      # writes nsk_worker_* to .env
11. docker compose --profile workers up -d ga-worker
12. deploy/scripts/smoke.sh                                          # post-deploy verification
```

### Redeploy

```
ssh droplet
cd /opt/nasrudin
git pull
docker compose pull
docker compose build
docker compose up -d
docker compose run --rm api /usr/local/bin/migrate    # if migrations pending
```

`/data` untouched. RocksDB hot cache survives. Theorems in Postgres untouched. Workers reconnect within 5 s of API readiness.

### Path to App Platform

`docker-compose.yml` translates to `.do/app.yaml`:
- Each `services:` entry → App Platform Service component.
- `ga-worker` → Worker component.
- `backup` → Job with cron schedule.
- `volumes: data:` → App Platform Volume.
- Caddy disappears (App Platform edge handles ingress).
- Postgres → DO Managed Postgres (env-var swap only).

Migration is deploy-config, not code.

## Testing

### Unit tests
| Crate | New unit tests | Asserts |
|---|---|---|
| `crates/api/src/handlers/ingest.rs` | batch validation, dedup short-circuit, auth gating, per-worker rate limit, axiom/sorry pre-flight | every 4xx has structured error body; no path bypasses bearer; pre-flight catches `axiom Foo : T` and ` sorry` in any indentation |
| `crates/api/src/reverify.rs` | A→B fallback ordering, ChainMismatch detection, retry budget, contributor counter increment in same tx | A-passes-but-different-canonical = `Rejected{ChainMismatch}`; verified theorem increments `workers.theorems_contributed` exactly once |
| `crates/api/src/handlers/events.rs` | two-stream split, event filtering | `discoveries` stream gets `theorem_*` only; `stats` stream gets `ga_status_tick` and `worker_heartbeat` only |
| `crates/api/src/handlers/seed.rs` | axiom catalog response shape, top-N seed selection | empty domain returns 404; valid domain returns axioms + ≤N theorems |
| `crates/pg/src/query/theorems.rs` | hash dedup, status transitions, contributor attribution, cursor pagination, fitness filter | Pending→Verified emits broadcast; Pending→Pending is no-op; cursor is stable under inserts |
| `crates/pg/src/query/workers.rs` | heartbeat update, contribution increment, list_all ordering | `theorems_contributed` increment is atomic with theorem update |
| `crates/rocks` | extend with reverify_queue CF round-trip | queue persists across `Drop`+reopen |

### Integration tests (testcontainers, real Postgres + RocksDB)
- `tests/ingest_pipeline.rs` — Reverify Queue against stub Lake Builder. Postgres + RocksDB consistent on every transition.
- `tests/hydration.rs` — 1000 verified theorems in Postgres, drop RocksDB, boot → all 1000 in RocksDB.
- `tests/dedup.rs` — same `canonical_hash` from two workers concurrently → one accepted, the other 409 with same id.
- `tests/storage_inconsistency.rs` — simulate Postgres-ok-RocksDB-fail; next hydration reconciles, no data loss.

### End-to-end (real Lake Builder, nightly)
`engine/tests/e2e/spontaneous_emc2_ingest.rs`:
1. docker-compose up (test stack).
2. Issue worker key.
3. POST `RestEnergyUpstream.lean` to `/api/ingest`.
4. Poll `/api/theorems/<hash>` until `Verified` (≤180 s).
5. Assert SSE feed received `theorem_pending` then `theorem_verified` with matching ids.
6. Restart API container; re-fetch — still `Verified`.
7. Drop `/data/rocks/`, restart, re-fetch — still `Verified` (hydration path).

### Smoke tests (post-deploy)
`deploy/scripts/smoke.sh`:
```
✓ GET  https://nasrudin.org/                                  → 200, contains "Nasrudin"
✓ GET  https://api.nasrudin.org/health                        → 200, {db:ok, rocks:ok, queue_depth:N}
✓ GET  https://api.nasrudin.org/api/theorems?limit=1          → 200
✓ GET  https://api.nasrudin.org/api/theorems/<known-hash>/lean→ 200, text/plain
✓ GET  https://api.nasrudin.org/api/domains                   → 200
✓ GET  https://api.nasrudin.org/api/axioms                    → 200
✓ GET  https://api.nasrudin.org/api/workers                   → 200
✓ GET  https://api.nasrudin.org/api/events/discoveries        → 200, ≥1 keep-alive in 20s
✓ GET  https://api.nasrudin.org/api/events/stats              → 200, ≥1 keep-alive in 20s
✓ POST https://api.nasrudin.org/api/ingest (test key, batch=1)→ 202
✓ poll until Verified                                         → ≤180s
✓ POST ingest with `axiom` in lean_source                     → per-theorem `Rejected{axiom_or_sorry_in_source}`
```

### Frontend tests
- `tsc --noEmit && biome check` (existing). The frontend already calls `useRecentTheorems`, `useTheorem`, `useMe`, `useApiKeys`, `useSavedSearches`, `useWorkers`, `useMeStats`. Making the server contract match each `Theorem`/`Worker`/etc. TypeScript type ensures existing pages render. No new component tests required.
- New SSE hooks (`useDiscoveryFeed()`, `useStatsStream()`) covered by a smoke check in `smoke.sh` (event received within 20 s of opening the stream).

### Load test (one-time, pre-launch)
`wrk` against `/api/ingest` and `/api/theorems`. Targets:
- Ingest: queue depth steady < 50 with one GA worker submitting.
- Reads: 200 RPS on `/api/theorems?limit=50` from 100 clients, p95 < 300 ms.

Numbers go in `docs/RUNBOOK.md` as the baseline.

## Acceptance criteria

Phase 9 is complete when **all** hold simultaneously on the live droplet at `nasrudin.org`:

1. **Landing + browse.** `https://nasrudin.org` renders the landing page; `/browse` shows live theorems from Postgres including the backfilled hand proofs and the GA-discovered theorems from prior iterations.
2. **Theorem detail + Lean download.** `/theorem/<id>` renders the full proof tree; `GET https://api.nasrudin.org/api/theorems/<hash>/lean` returns the `.lean` file with `Content-Type: text/plain`, downloads correctly from the page's "Download .lean" button, and the downloaded file builds standalone via `lake build` against the committed `prover/` tree.
3. **In-process ingest.** `POST /api/ingest` from the in-process GA worker results in a `Verified` row in Postgres within 180 s of submission, broadcast on `/api/events/discoveries`.
4. **SSE on both streams.** `EventSource('https://api.nasrudin.org/api/events/discoveries')` receives `theorem_verified` events live; `EventSource('.../api/events/stats')` receives `worker_heartbeat` and `ga_status_tick` events live.
5. **Contributor counter.** Submitting a verified theorem from worker `W` increments `workers.theorems_contributed` for `W` atomically; `/api/workers` reflects the new count; `/leaderboard` shows the worker.
6. **B-path firewall.** Submitting a `lean_source` containing a fresh `axiom` or `sorry` is rejected at ingest with `Rejected{axiom_or_sorry_in_source}`, never reaches lake build.
7. **Per-worker rate limit.** Submitting > 60 theorems/min from a single worker key returns `429` with `X-RateLimit-Reset` header.
8. **Frontend endpoint coverage.** `GET /api/me/stats`, `GET /api/saved-searches`, `GET /api/workers`, `GET /api/domains`, `GET /api/axioms`, `GET /api/api-keys` all return 200 with shapes matching `nasrudin-frontend/src/lib/types.ts`. `tsc --noEmit && biome check` pass on the frontend with no `any`-typed API responses.
9. **Redeploy persistence.** `git pull && docker compose up -d` redeploys without losing data — verified by counting theorems before and after.
10. **RocksDB rehydrate.** `docker compose down && rm -rf /data/rocks && docker compose up -d` rebuilds RocksDB from Postgres and serves the same theorems.
11. **Backups present.** Hourly Spaces backup contains both `pg_dump` and `rocks/` for the last 24 h; `restore-from-spaces.sh` against an empty droplet successfully reconstitutes the corpus.
12. **Smoke test.** `deploy/scripts/smoke.sh` passes end-to-end (all eight assertions from the testing section).
13. **Existing milestones preserved.** Backfill script ingestion of `prover/PhysicsGenerator/Derived/*.lean` results in those theorems being browsable via `/browse` and downloadable via `/api/theorems/<hash>/lean`.
14. **GA worker is API-only.** `crates/ga/src/bin/discover_emc2.rs` writes **zero** files to `prover/PhysicsGenerator/Derived/Discover*.lean` going forward — all output goes through `/api/ingest`. (The pre-existing `Discover*.lean` files committed before Phase 9 are preserved via backfill.)

The fourteenth criterion is the hard line: if the GA worker still writes new Lean files locally, ingest isn't load-bearing yet.

## Open questions

None at design-approval time. Implementation-time decisions (table column types, SeaORM relation cardinalities, exact tokio task supervisor types, Caddy global options) defer to the implementation plan.
