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

- Multi-worker leaderboards beyond a simple `verified_count` per worker.
- LLM-guided exploration via MCP (`crates/mcp` stays a stub).
- Importer crate work (`crates/importer` not touched).
- Public release of the standalone worker binary (deferred to Phase 10).
- Auto-scaling. Single droplet, vertical scale only. Horizontal scaling is by way of users running their own worker binary in Phase 10+.

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
                   ┌──────────────────────┐
                   │ Remote workers       │ download nasrudin-worker
                   │ POST /api/ingest     │ same contract as in-proc
                   │ GET  /api/theorems   │ hydrate local RocksDB
                   │ SSE  /api/sse        │ live theorem feed
                   └──────────────────────┘
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

- `crates/core` — `Expr`, `Theorem`, `ProofTree`, `TheoremId`, `Domain`. No changes.
- `crates/rocks` — `TheoremDb` with 9 existing column families (theorems, proofs, lineage, by_domain, by_depth, by_axiom, by_generation, latex_index, stats). Phase 9 adds **one new column family**: `reverify_queue` (key = job id, value = serialised `ReverifyJob{theorem_id, attempts, enqueued_at}`). Persisting the queue in RocksDB means in-flight jobs survive API restarts; the drain task scans this CF on boot and resumes work. Also adds boot-time hydration of theorem CFs from Postgres if empty.
- `crates/derive` — `AxiomStore`, `Chain`, `RuleStep`, `lean_emitter`. Used by the A-path regen step in the Reverify Queue. No structural changes.
- `crates/api` — auth, api_keys, workers/register handlers stay. New handlers added under `crates/api/src/handlers/` for ingest, theorems, sse, heartbeat.
- `crates/pg` — SeaORM 2 setup, existing entities (users, sessions, api_keys, workers, saved_searches, user_preferences). Migration framework already in place.

### New or substantially changed

| Component | What's new |
|---|---|
| `crates/api/src/handlers/ingest.rs` | New. `POST /api/ingest` handler. |
| `crates/api/src/handlers/theorems.rs` | New. `GET /api/theorems`, `GET /api/theorems/recent`, `GET /api/theorems/:id`, `GET /api/theorems/:hash/lean`. |
| `crates/api/src/handlers/sse.rs` | New. `GET /api/sse` event-stream over `discovery_tx` broadcast. |
| `crates/api/src/handlers/workers.rs` | Extended with `POST /api/workers/heartbeat`. |
| `crates/api/src/reverify.rs` | New. Queue drain, A→B fallback verification, status transitions. |
| `crates/api/src/lake_builder.rs` | New. Tokio task pool that runs `lake build` in tmpdir copies of `prover/`. |
| `crates/api/src/hydration.rs` | New. Boot-time RocksDB hydration from Postgres. |
| `crates/pg` migrator | New migration: `theorems` table (mirror of RocksDB record). |
| `crates/pg/src/query/theorems.rs` | New. Insert, dedup-by-hash, status update, list-with-cursor. |
| `crates/ga/src/bin/discover_emc2.rs` | Modified. Replace file-write path with HTTP POST to `/api/ingest`. |
| `nasrudin-frontend/src/lib/queries.ts` | Extended with `useTheoremStream()` SSE hook; existing `useRecentTheorems`/`useTheorem` need only server-side endpoints to be implemented to match. |
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

`POST /api/ingest`. Authentication via `Authorization: Bearer nsk_worker_*`.

```json
{
  "canonical_statement": "E = m * c^2",
  "chain": [
    {"type": "IntroduceAxiom", "axiom_name": "four_momentum_time_component"},
    {"type": "IntroduceAxiom", "axiom_name": "minkowski_invariant_def"},
    {"type": "IntroduceAxiom", "axiom_name": "invariant_mass_postulate"},
    {"type": "IntroduceAxiom", "axiom_name": "rest_frame_psq_zero"},
    {"type": "RearrangeEquation", "target": "...", "description": "..."},
    {"type": "TakePositiveRoot"}
  ],
  "lean_source": "import PhysicsGenerator.Axioms\n\ntheorem rest_energy ...\n  := by ...",
  "domain": "SpecialRelativity",
  "axioms_used": ["four_momentum_time_component", "minkowski_invariant_def", "invariant_mass_postulate", "rest_frame_psq_zero", "c_positive", "mass_nonneg", "energy_nonneg"],
  "engine_git_sha": "cffe109",
  "contributor_id": "in-proc-worker-1"
}
```

Response on accept: `202 Accepted` with `{"theorem_id": "<hex>", "status": "Pending"}`.

Response on dedup: `409 Conflict` with `{"theorem_id": "<hex>", "status": "Verified"}` (the existing record).

## Trust model — A-first, B-fallback hybrid

Two phases: synchronous validation in the ingest handler, then asynchronous verification on dequeue.

**Synchronous (ingest handler, cheap, < 50 ms):**
1. Bearer-key authentication.
2. Schema + size validation.
3. **Dedup**: `canonical_hash(canonical_statement)` against Postgres. If found, return `409 Conflict` with the existing `theorem_id` — no enqueue, no insert.
4. INSERT theorem with `status = Pending`. Broadcast `theorem_pending` on SSE. Return `202 Accepted` with the new `theorem_id`.
5. Enqueue `{theorem_id, attempts: 0}` into the `reverify_queue` CF.

**Asynchronous (Reverify Queue drain, slow, ≤ 300 s per job):**
1. **A-path (optimistic)**: regenerate Lean from `chain` via the server's own `AxiomStore` + `lean_emitter`. Run `lake build`. If it compiles AND the proven theorem matches `canonical_statement` → **accept**, store regenerated Lean as canonical, mark `Verified`.
2. **B-path (fallback)**: if A failed for any reason — unknown `RuleStep` variant, regen Lean doesn't compile, regen theorem mismatches `canonical_statement` — run `lake build` on the worker-submitted `lean_source`. If it compiles AND it proves `canonical_statement` → **accept**, store worker's Lean as canonical, mark `Verified`, log `server_emitter_drift{engine_git_sha=...}`.
3. **Reject** with `Rejected{reason}` if both fail. Status flip to `Rejected` is broadcast on SSE so frontend can update.

By the time the queue drain runs, dedup has already happened — the row in Postgres carries the canonical hash, so re-running dedup at dequeue time is unnecessary.

**Why hybrid:** the artifact the network is collecting is a *theorem* — `(statement, lean-proof, axioms-used)`. The chain is the GA's path; two different chains can yield the same theorem. Once the Lean source compiles in Lean 4 + Mathlib, the math is real. A-first regeneration adds provenance validation when versions align; B-fallback ensures forward-compatibility across engine versions.

## Data flow

### Ingest

```
GA Worker            Axum API                 Reverify Queue       Lake Builder         Postgres + RocksDB     SSE clients
    │                    │                         │                    │                       │                    │
    ├── POST /api/ingest ►                         │                    │                       │                    │
    │                    ├── verify worker key ────────────────────────────────────────────────►│                    │
    │                    ├── canonical_hash dedup ─────────────────────────────────────────────►│                    │
    │                    ├── INSERT theorem(Pending) ──────────────────────────────────────────►│                    │
    │                    │                         │                    │                       ├── theorem_pending ►│
    │   202 Accepted ◄───┤                         │                    │                       │                    │
    │                    ├── enqueue ──────────────►                    │                       │                    │
    │                    │                         ├── A-path: regen ───►                       │                    │
    │                    │                         │                    ├── lake build (~60s) ──┤                    │
    │                    │                         │   if A passes ─────────────────────────────►│                   │
    │                    │                         │                    │                       ├── theorem_verified►│
    │                    │                         │   if A fails: B ───►                       │                    │
    │                    │                         │                    ├── lake build ─────────┤                    │
    │                    │                         │   if B passes ─────────────────────────────►│  log drift alarm  │
    │                    │                         │                    │                       ├── theorem_verified►│
    │                    │                         │   if both fail ────────────────────────────►│                   │
    │                    │                         │                    │                       ├── theorem_rejected►│
```

### Boot / hydration

API connects Postgres → runs migrations → opens RocksDB → counts theorems in RocksDB. If empty, `SELECT * FROM theorems WHERE status='Verified'`, `TheoremDb::put_theorem` for each row, then `API ready`. Idempotent — restartable mid-hydration.

### Read

Frontend SSR hits `GET /api/theorems?domain=sr&limit=50` and `GET /api/theorems/recent?limit=50` — both already wired in `nasrudin-frontend/src/routes/browse.tsx`. Server reads RocksDB hot path for indexed queries; falls back to Postgres for SQL-only filters (e.g. by_contributor, leaderboard). Hash-to-id mapping lives in Postgres because `canonical_hash` is a Postgres-natural lookup. `.lean` download endpoint reads `proof.lean_source` from RocksDB.

### SSE

Existing `discovery_tx: broadcast::Sender<DiscoveryEvent>` in `state.rs`. Add new event variants: `theorem_pending`, `theorem_verified`, `theorem_rejected`, `ga_status_tick`. New `useTheoremStream()` hook in frontend `lib/queries.ts` opens `EventSource('/api/sse')` and calls `queryClient.invalidateQueries({queryKey: ['theorems']})` on relevant events.

### Backup

Backup container, every 1 h:
1. `pg_dump --format=custom postgres > /tmp/pg.dump`
2. `rclone sync /data/rocks/ spaces:nasrudin-backups/$(date +%Y/%m/%d/%H)/rocks/`
3. `rclone copy /tmp/pg.dump spaces:nasrudin-backups/$(date +%Y/%m/%d/%H)/postgres.dump`
4. Delete dumps older than 30 days on Spaces.

Restore: pull latest dir from Spaces to `/data`, `pg_restore`, `docker compose up -d`.

### Future remote-worker sync (Phase 10, sketch only)

Same `POST /api/ingest` contract. Cold start: `GET /api/theorems?since=<cursor>&limit=1000` paginated, then `GET /api/sse` for live deltas. No code path is special-cased for "remote".

## Failure modes

### Ingest validation
| Failure | HTTP | Response |
|---|---|---|
| Missing/malformed bearer | 401 | reject without enqueue |
| Non-worker key prefix | 403 | reject |
| Payload schema invalid | 400 | reject with field-level error |
| `canonical_hash` already in Postgres | 409 | dedup short-circuit, return existing record |
| `lean_source` > 256 KiB | 413 | reject |
| `chain` > 64 steps | 413 | reject |

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
4. Page Rule: `nasrudin.org/api/sse` → bypass cache, no-buffering.

### Bootstrap (fresh droplet)

```
1. doctl compute droplet create … --user-data deploy/scripts/bootstrap.sh
2. doctl compute volume-action attach <vol-id> <droplet-id>
3. ssh in, mount volume at /mnt/nasrudin-data
4. cd /opt/nasrudin (cloned by bootstrap.sh)
5. cp .env.example .env && edit secrets
6. docker compose pull && docker compose up -d
7. docker compose run --rm api /usr/local/bin/migrate
8. open https://nasrudin.org → landing renders, /browse empty but live
9. docker compose run --rm api /usr/local/bin/issue-worker-key  # writes to .env
10. docker compose --profile workers up -d ga-worker
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
| `crates/api/src/handlers/ingest.rs` | payload validation, dedup short-circuit, auth gating | every 4xx has structured error body; no path bypasses bearer |
| `crates/api/src/reverify.rs` | A→B fallback ordering, ChainMismatch detection, retry budget | A-passes-but-different-canonical = `Rejected{ChainMismatch}` |
| `crates/pg/src/query/theorems.rs` | hash dedup, status transitions, contributor attribution | Pending→Verified emits broadcast; Pending→Pending is no-op |
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
✓ GET https://nasrudin.org/                     → 200
✓ GET https://api.nasrudin.org/health           → 200, {db:ok, rocks:ok, queue_depth:N}
✓ GET https://api.nasrudin.org/api/theorems?limit=1 → 200
✓ GET https://api.nasrudin.org/api/sse          → 200, ≥1 keep-alive in 20 s
✓ POST https://api.nasrudin.org/api/ingest (test key) → 202
✓ poll until Verified                           → ≤180 s
```

### Frontend tests
- `tsc --noEmit && biome check` (existing). The frontend already calls `useRecentTheorems` / `useTheorem`; making the server contract match ensures the existing browse page works. No new component tests required.

### Load test (one-time, pre-launch)
`wrk` against `/api/ingest` and `/api/theorems`. Targets:
- Ingest: queue depth steady < 50 with one GA worker submitting.
- Reads: 200 RPS on `/api/theorems?limit=50` from 100 clients, p95 < 300 ms.

Numbers go in `docs/RUNBOOK.md` as the baseline.

## Acceptance criteria

Phase 9 is complete when **all** hold simultaneously on the live droplet at `nasrudin.org`:

1. `https://nasrudin.org` loads landing + `/browse` shows live theorems from Postgres.
2. `POST https://api.nasrudin.org/api/ingest` from the in-process GA worker results in `Verified` within 180 s.
3. SSE clients on `/api/sse` receive `theorem_verified` events live.
4. `git pull && docker compose up -d` redeploys without losing data — verified by counting theorems before and after.
5. `docker compose down && rm -rf /data/rocks && docker compose up -d` rebuilds RocksDB from Postgres and serves the same data.
6. Hourly Spaces backup contains both `pg_dump` and `rocks/` for the last 24 h.
7. `deploy/scripts/smoke.sh` passes end-to-end.
8. `crates/ga/src/bin/discover_emc2.rs` writes **zero** files to `prover/PhysicsGenerator/Derived/Discover*.lean` — all output goes through `/api/ingest`.

The eighth criterion is the hard line: if the GA worker still writes Lean files locally, ingest isn't load-bearing yet.

## Open questions

None at design-approval time. Implementation-time decisions (table column types, SeaORM relation cardinalities, exact tokio task supervisor types, Caddy global options) defer to the implementation plan.
