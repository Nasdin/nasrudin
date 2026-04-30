# Cluster Steerer + Paid Researcher — Design

**Date:** 2026-04-30
**Phase:** Post Phase 9 (distributed platform). Builds on the 3-state verification, lazy lake-promotion, reputation, conjecture, and `/api/seed` ETag infrastructure shipped in Phase 9.
**Status:** Approved in brainstorming; ready for plan.

---

## Goal

Two coupled features that turn the Nasrudin cluster from "GA explores randomly" into "GA exploration is steered by user demand AND paid customers can buy directed proof-search":

1. **Cluster steerer** — an LLM (Kimi 2.6 via DO Gradient) reads aggregate user demand signals every 10 minutes and emits a validated `SteeringConfig` that workers hot-reload alongside `/api/seed`. Closed-loop feedback: outcomes from each cycle feed back into the next prompt.
2. **Paid Researcher slices** — $19/mo customers submit a conjecture they can't prove; a 96 lake-slot-hour quota of cluster GA capacity attempts to evolve a Lean-verified proof over up to 24 hours. Built on the existing `conjecture_jobs` spine (`engine/crates/pg/src/entity/conjecture_jobs.rs`).

The two features are coupled through the steerer's mode switch: when paid jobs are running, the steerer locks mutation knobs so paid-slice lake capacity stays predictable.

## Non-goals

- Replacing `nasrudin_llm`'s existing per-user provider/key flow (Anthropic / OpenAI / Ollama for user-initiated conjectures stays as-is).
- Manual admin approval of steering decisions. Fully automatic by design; admin tools are observation only.
- Multi-region cluster scheduling. One DO droplet, one explorer fleet, one paid-job queue.

---

## Component map

```
┌─────────────────────────────────────────────────────────────────────┐
│ API daemon (engine/crates/api)                                       │
│                                                                      │
│  ┌──────────────┐   ┌─────────────────┐   ┌───────────────────────┐ │
│  │ Demand probe │──▶│ Cluster steerer │──▶│ /api/steering         │ │
│  │ (signal agg) │   │ (Kimi via       │   │ ETag, ArcSwap         │ │
│  │              │   │  Gradient REST) │   └─────────┬─────────────┘ │
│  └──────────────┘   └────────▲────────┘             │               │
│                              │ outcome              │               │
│                     ┌────────┴────────┐             │               │
│                     │ cluster_steering│             │               │
│                     │ (PG, last 1000) │             │               │
│                     └─────────────────┘             │               │
│                                                     │               │
│  ┌──────────────────┐  ┌──────────────────────┐     │               │
│  │ Paid job queue   │  │ /api/jobs/claim      │     │               │
│  │ (conjecture_jobs │──│ (atomic claim+lease) │◀────┼───┐           │
│  │  + quota tracker)│  │ /api/research/jobs/  │     │   │           │
│  └──────────────────┘  │   {id}/events (SSE)  │     │   │           │
│                        └──────────────────────┘     │   │           │
└─────────────────────────────────────────────────────┼───┼───────────┘
                                                      │   │
                                       ┌──────────────┼───┼──────────┐
                                       │ Worker       ▼   │          │
                                       │ ┌────────────────┴───────┐  │
                                       │ │ Steering ArcSwap       │  │
                                       │ │ (domain weights, etc.) │  │
                                       │ └────────────────────────┘  │
                                       │ ┌────────────────────────┐  │
                                       │ │ Job slot scheduler:    │  │
                                       │ │  - paid slice (claimed)│  │
                                       │ │  - explorer fleet (10% │  │
                                       │ │    floor, rest residual)│ │
                                       │ └────────────────────────┘  │
                                       └─────────────────────────────┘
```

---

## Cluster steerer

### Provider: DigitalOcean Gradient

A new `nasrudin_llm` provider — `engine/crates/llm/src/gradient.rs` — implementing the `LlmProvider` trait against the Gradient REST API.

- Base URL: `https://inference.do-ai.run/v1/`. Endpoints used: `POST /chat/completions` (same shape as OpenAI), `GET /models` (boot-time model availability check).
- Auth: `Authorization: Bearer ${GRADIENT_API_KEY}`. Server-owned key in env (NOT a user-stored encrypted key). Different invocation site from existing per-user providers.
- Default model id: `kimi-k2-instruct`. Configurable via `STEERER_MODEL` env. On boot the steerer pings `GET /models` and panics if the configured id isn't present, with a clear error message listing what IS available so swapping is one env var.
- Fallback model: `STEERER_MODEL_FALLBACK` env (e.g. `llama-3.3-70b-instruct`). Used when the primary errors three cycles in a row.
- Doctl is NOT used at runtime — installed `doctl` (1.120.2) doesn't have `genai` subcommands; 1.155.0+ does. We talk to Gradient over HTTPS directly. doctl is only a deploy-time convenience.

### Cycle

Every 10 minutes (configurable via `STEERER_CADENCE_SECONDS`):

1. **Close out previous cycle.** Read `cluster_steering` row with `ended_at IS NULL`. Compute `outcome_json` from RocksDB + PG counters captured during the cycle. Set `ended_at = now()`.
2. **Determine mode.** Query `conjecture_jobs WHERE state IN ('claimed','running') AND lease_expires_at > now()`. ≥1 row → mode B (mutation knobs locked). Zero rows → mode C (full authority).
3. **Build prompt.** System prompt = role + JSON schema + guard rails. User prompt =
   - `history`: last 10 (config_json, outcome_json) pairs from `cluster_steering`, oldest first.
   - `current_demand`: aggregated signals (see below).
   - `current_population`: GA stats (population diversity, fitness percentiles, domain mix).
   - `active_jobs`: snapshot of running paid jobs with `{domain, conjecture_summary}` (no PII).
   - `scope`: `"B"` or `"C"`.
4. **Call Kimi.** `temperature=0.4`, `max_tokens=2048`, `response_format=Json` with the schema enforced server-side too.
5. **Validate.** Parse against `SteeringConfig` JSON schema. On parse fail OR validation fail (e.g., simplex doesn't sum to 1, mutation knob out of range, hard target in mode B): log + emit `steerer_validation_fail` metric, fall back to last-known-good config, write a `cluster_steering` row marked `validation_failed: true`.
6. **Persist + publish.** Insert new `cluster_steering` row with the new config + `started_at = now()`, `ended_at = null`. Bust the `/api/steering` ETag. Workers pick it up on next chunk boundary.

### `SteeringConfig` schema

```json
{
  "version": 1,
  "scope": "B" | "C",
  "domain_weights": { "special_relativity": 0.1, "electromagnetism": 0.4, ... },  // sums to 1.0
  "axiom_emphasis": { "<axiom_name>": 0.0..2.0 },                                 // multiplier on selection prob
  "fitness_weights": {
    "novelty": 0.0..1.0,
    "dimensional_elegance": 0.0..1.0,
    "chain_length_penalty": 0.0..1.0,
    "target_proximity": 0.0..1.0
  },                                                                               // sums to 1.0
  "soft_targets": [{ "latex": "δQ = T·dS", "domain": "thermodynamics", "weight": 0.3 }],
  "hard_targets": [{ "latex": "...", "domain": "...", "weight": 0.5 }],            // C-only; rejected in B
  "mutation_knobs": {                                                               // C-only; null in B
    "rate": 0.05..0.30,
    "suffix_bias": 0.0..1.0,
    "population_size": 32..512,
    "elitism_fraction": 0.0..0.2
  },
  "rationale": "≤500 chars why Kimi chose this"
}
```

Hard ranges enforced server-side. Anything out of range → fall back to last-known-good.

### `OutcomeJson` shape

Computed at cycle close from RocksDB scans + PG counters:

```json
{
  "theorems_verified_in_window": 142,
  "domain_distribution_actual": { "sr": 0.18, "em": 0.52, "qm": 0.20, "gr": 0.10 },
  "target_hit_rate": 0.12,                                  // cosine of new theorems vs targets
  "population_diversity_delta": -0.04,                       // fitness variance now vs cycle start
  "cascade_rejects": 3,
  "lake_failure_rate": 0.04,
  "user_engagement": {
    "views": 81,
    "downloads": 12,
    "manual_verifies": 4,
    "median_dwell_ms": 4200
  },
  "fresh_demand_signals": {
    "top_searches": ["entropy", "second law", "Carnot"],
    "top_saved_searches_this_window": [...],
    "top_concept_queries": [...]
  }
}
```

### Demand signal sources

All already exist:

- `pg::query::search` — search log of LaTeX queries from `/api/search`.
- `pg::query::saved_searches` — persistent user saves.
- `pg::query::targeted_search_usage` — paid concept searches.
- `handlers/concept_search.rs` — semantic search hits.
- `handlers/theorems.rs` — view + download counters (need lightweight increment in handlers; today it's not tracked).
- `handlers/manual_verify.rs` — manual lake-verify clicks (already exists).

Aggregator runs in-process, reads from PG with 60s windows, builds a histogram for the prompt. Caps top-N at 10 for prompt size.

### Storage

```sql
CREATE TABLE cluster_steering (
    id           UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    started_at   TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    ended_at     TIMESTAMPTZ,
    scope        TEXT NOT NULL CHECK (scope IN ('B', 'C')),
    config_json  JSONB NOT NULL,
    outcome_json JSONB,
    validation_failed BOOLEAN NOT NULL DEFAULT FALSE,
    model_id     TEXT NOT NULL,
    prompt_tokens   INT,
    completion_tokens INT
);
CREATE INDEX cluster_steering_started_at_idx ON cluster_steering (started_at DESC);
```

Pruned to the most recent 1000 rows by a daily cron in the API daemon (`DELETE WHERE started_at < (SELECT started_at FROM cluster_steering ORDER BY started_at DESC OFFSET 1000 LIMIT 1)`).

### Distribution

- New endpoint: `GET /api/steering` → `{ config, etag, mode, started_at }`. Honors `If-None-Match` for 304s.
- ETag = xxhash64 of `config_json`. Cached server-side in `Arc<RwLock<(Etag, ConfigJson)>>`; refreshed when the steerer writes a new row.
- Folded into `/api/seed` response under a `steering` field so workers fetch both in one round-trip. The seed ETag changes whenever steering changes.
- Worker side: `engine/crates/ga/src/bin/worker.rs` already polls `/api/seed` per chunk. Add an `ArcSwap<SteeringConfig>` next to the existing `ArcSwap<AxiomStore>`. Hot-reload on every poll.
- Mutation knob plumbing: `engine/crates/ga/src/chain_engine.rs` reads from the steering ArcSwap before each generation. Population size changes take effect at next chunk boundary (NOT mid-generation; mid-generation resize is too disruptive).

---

## Paid Researcher slices

Build on existing `conjecture_jobs` table — most fields already match the design. Additions needed:

- `lake_slot_hours_quota INT NOT NULL DEFAULT 96` — total quota for this job.
- `lake_slot_hours_consumed REAL NOT NULL DEFAULT 0.0` — running tally updated by claim+heartbeat.
- `slice_priority INT NOT NULL DEFAULT 5` — for queue ordering when multiple jobs compete.
- `tier TEXT NOT NULL DEFAULT 'researcher'` — billing tier; lets us add higher tiers later without migration.

The existing `budget` JSONB column (carrying `BudgetSpec { wall_seconds, max_candidates }`) stays — those are still meaningful caps for the per-job GA loop. The new `lake_slot_hours_*` columns sit alongside as the cluster-capacity accounting view: `lake_slot_hours_remaining = quota - consumed`.

### Job lifecycle

```
created (POST /api/research/jobs)
   │
   ▼ user provides hunch (LaTeX or natural language)
queued
   │
   ▼ worker calls /api/jobs/claim with capacity
claimed (lease 5 min, heartbeat every 30s)
   │
   ▼ worker reports candidates_attempted, lake_slot_hours_consumed via heartbeat
running
   │
   ├──▶ Lean-verified proof found
   │       state=proved, outcome="proved", verified_theorem_ids populated, completed_at set
   │
   ├──▶ wall_seconds elapsed OR lake_slot_hours_consumed ≥ quota
   │       state=budget_exhausted, outcome="budget_exhausted",
   │       best partial chain saved as a regular Theorem (status=ChainVerified),
   │       credit refunded to user account
   │
   └──▶ lease_expires_at < now() AND no heartbeat in 5 min
           state=queued (worker died; another can claim)
```

### Worker pickup protocol

New endpoint: `POST /api/jobs/claim`

Request:
```json
{
  "worker_id": "<api-key fingerprint>",
  "available_lake_slots": 4,
  "domains_supported": ["special_relativity", "electromagnetism"]
}
```

Response (success):
```json
{
  "job_id": "<uuid>",
  "hunch": "...",
  "domain_hint": "...",
  "axiom_set": [...],
  "initial_population": [...],
  "mutation_priors": {...},
  "target_shape": "...",
  "lake_slot_hours_remaining": 92.5,
  "lease_expires_at": "...",
  "heartbeat_url": "/api/jobs/{id}/heartbeat"
}
```

Response when no jobs available: `204 No Content`. Worker falls through to explorer-fleet duty.

The claim is **atomic** — `UPDATE conjecture_jobs SET claimed_by=?, claimed_at=now(), lease_expires_at=now()+interval '5 min', state='claimed' WHERE id=(SELECT id FROM conjecture_jobs WHERE state='queued' AND lake_slot_hours_remaining > 0 ORDER BY slice_priority DESC, created_at ASC LIMIT 1 FOR UPDATE SKIP LOCKED) RETURNING *`.

Per-worker fairness: a worker holding ≥1 active claim can't claim a second job until it completes one. Prevents one worker hoarding paid slots.

### Heartbeat

`POST /api/jobs/{id}/heartbeat`:
```json
{
  "candidates_attempted_delta": 12,
  "candidates_verified_delta": 1,
  "lake_slot_hours_consumed_delta": 0.083,
  "current_best_fitness": 0.62,
  "current_best_chain_length": 4
}
```

Response: `{ continue: true | false, reason: "..." }`. Sets `continue=false` if budget exhausted, lease lost, or admin-cancelled.

Lease extended by 5 min on each heartbeat. Worker calls every 30s. The worker computes `lake_slot_hours_consumed_delta = (seconds_since_last_heartbeat / 3600.0) * slots_held_for_this_job` and sends it raw; the API trusts it but caps at `2 * (delta_wallclock_s / 3600) * slots_held` server-side as a sanity ceiling.

### SSE for the user

`GET /api/research/jobs/{id}/events` — Server-Sent Events stream. Auth: cookie session OR API key, must own the job.

Event types:
- `job_state` — fired on every state transition.
- `progress` — fired on every heartbeat. `{ candidates_attempted, candidates_verified, best_fitness, best_chain_summary }`.
- `theorem_verified` — fired when a chain in this job's lineage hits ChainVerified. `{ theorem_id, statement_latex }`.
- `proved` — terminal. Includes `.lean` URL.
- `budget_exhausted` — terminal. Includes best-partial summary + refund credit amount.

### Quota math

- 1 lake-slot-hour = 1 lake-build slot occupied for 1 hour.
- $19/mo Researcher tier = 1 conjecture job/month default = 96 lake-slot-hours = 4 slots × 24 h.
- Soft floor: 10% of cluster's total lake-slot capacity is reserved for explorer fleet at all times. Computed dynamically: `min_explorer_slots = max(2, floor(cluster_total_slots * 0.10))`.
- A worker decides per-poll: if its `available_lake_slots > 0` AND the cluster's `current_explorer_floor_satisfied` AND a paid job is queued → claim. Otherwise → explorer-fleet duty.
- The "explorer floor satisfied" check: API tracks `total_lake_slots_in_cluster` (sum of latest reported `available_lake_slots` from each worker in last 5 min) and `lake_slots_currently_on_paid_jobs` (sum of active claims). Floor satisfied iff `(total - on_paid) >= min_explorer_slots`.

### Refund / credit

On `budget_exhausted`:
- If `candidates_verified == 0` and `candidates_attempted < 1000` → full refund (1 credit returned to user pool).
- If partial progress → no refund, but the best partial chain is published as a regular ChainVerified theorem under the user's name (so they get attribution + the corpus benefits).

Implementation: `users.research_credits INT NOT NULL DEFAULT 1` column added in migration. Stripe webhook on monthly renewal sets to `1`. Job creation decrements. Refund increments.

### Storage delta

```sql
ALTER TABLE conjecture_jobs
  ADD COLUMN lake_slot_hours_quota INT NOT NULL DEFAULT 96,
  ADD COLUMN lake_slot_hours_consumed REAL NOT NULL DEFAULT 0.0,
  ADD COLUMN slice_priority INT NOT NULL DEFAULT 5,
  ADD COLUMN tier TEXT NOT NULL DEFAULT 'researcher';
CREATE INDEX conjecture_jobs_queue_idx
  ON conjecture_jobs (state, slice_priority DESC, created_at ASC)
  WHERE state = 'queued';

ALTER TABLE users
  ADD COLUMN research_credits INT NOT NULL DEFAULT 0;
```

---

## Endpoints (full inventory)

| Method | Path | Auth | Purpose |
|--------|------|------|---------|
| `GET`  | `/api/steering` | none (public read) | Current `SteeringConfig` + ETag |
| `GET`  | `/api/seed` | none | Existing — now includes `steering` field |
| `POST` | `/api/research/jobs` | session OR API key | Create paid job (decrements `research_credits`) |
| `GET`  | `/api/research/jobs` | session OR API key | List your jobs |
| `GET`  | `/api/research/jobs/{id}` | session OR API key | Job detail |
| `GET`  | `/api/research/jobs/{id}/events` | session OR API key | SSE progress stream |
| `POST` | `/api/research/jobs/{id}/cancel` | owner | User-initiated cancel; refund applies |
| `POST` | `/api/jobs/claim` | worker key | Atomic claim with lease |
| `POST` | `/api/jobs/{id}/heartbeat` | worker key, must hold lease | Progress + lease extension |
| `POST` | `/api/jobs/{id}/release` | worker key, must hold lease | Voluntary release |
| `GET`  | `/api/admin/steering/recent` | ADMIN_TOKEN | Last 50 cycles for ops review |
| `POST` | `/api/admin/steering/force` | ADMIN_TOKEN | Override config; persists as a manual cycle |

---

## Error handling

- **Gradient API down.** Steerer logs, emits `steerer_provider_error` metric, reuses last-known-good config. After 3 consecutive failures, falls over to `STEERER_MODEL_FALLBACK`. After 6 consecutive failures, alerts (Sentry / log alert) and stays on last-known-good.
- **Validation fail.** As above — last-known-good, row marked `validation_failed: true`, metric incremented.
- **No `cluster_steering` rows yet (cold start).** Steerer uses a hard-coded default `SteeringConfig` for the first cycle. Default = uniform domain weights, all axiom emphasis = 1.0, balanced fitness weights, no targets, default mutation knobs.
- **Worker claims a job then dies.** Lease expires after 5 min without heartbeat. Cron task in API (`reap_dead_leases`) runs every minute, sets `state=queued` for jobs whose `lease_expires_at < now()`. Another worker picks up.
- **User cancels mid-job.** Job goes to `cancelled` state; worker's next heartbeat returns `continue: false`; worker drops the slice, picks up next job. User gets full refund.
- **Multiple workers race to claim same job.** `FOR UPDATE SKIP LOCKED` on the queue query guarantees one winner.
- **Quota math drift.** Heartbeat increments are floats; PG `REAL` is fine for the precision needed (~6 decimal digits is way more than 96 hours / 0.001-hour resolution).

---

## Testing

### Unit

- Steerer: feed canned demand + history JSON, mock Gradient response, assert `SteeringConfig` round-trips, assert validation rejects out-of-range values, assert mode B drops mutation knobs.
- Quota math: heartbeat accumulation, budget exhaustion trigger, refund computation.
- Atomic claim: two parallel claim calls with one queued job → one wins, one gets 204.

### Integration

- Boot API + 2 workers + faked Gradient responder (returns valid configs). Run 30 min of simulated 10-min cycles. Assert `cluster_steering` table has 3 rows, ETag changes between rows, workers' ArcSwap shows latest config.
- Submit a paid job via `POST /api/research/jobs`. Worker claims it. Heartbeat 10 cycles. Force success. Assert SSE stream emits `proved`, .lean artifact present, `verified_theorem_ids` populated.
- Submit, kill worker mid-job, assert reaper requeues, second worker claims, completes.
- Submit, exhaust budget without success, assert refund + best-partial published.

### Soak (24h)

- 1 paid job, 5 workers, 1000 simulated user search hits. Steerer cycles every 10 min, mode toggles correctly when paid job state changes, no worker starves the explorer floor, paid job completes (or budget-exhausts) within 24h.

---

## Observability

New `/metrics` gauges/counters:

- `nasrudin_steerer_cycles_total` (counter)
- `nasrudin_steerer_validation_fails_total` (counter)
- `nasrudin_steerer_provider_errors_total{model}` (counter)
- `nasrudin_steerer_mode{scope}` (gauge, 1 for current scope, 0 otherwise)
- `nasrudin_paid_jobs_active` (gauge)
- `nasrudin_paid_jobs_queued` (gauge)
- `nasrudin_paid_jobs_lake_slot_hours_consumed_total` (counter)
- `nasrudin_explorer_floor_satisfied` (gauge, 0/1)
- `nasrudin_explorer_slot_count` (gauge — current residual)

Existing Grafana dashboard gets a "Cluster steering" panel and a "Paid jobs" panel.

---

## Open implementation details (defer to plan)

These don't change the architecture but the plan needs to address them:

1. **Conjecture compilation.** Existing `conjecture/orchestrate.rs` already takes a free-text `hunch`. For paid jobs, do we accept LaTeX, Lean source, or both? Likely both — let the LLM phase compile LaTeX → `Expr` skeleton just like today's flow, but pin `target_shape` to the user's input.
2. **Refund mechanism details.** Is `research_credits` enough, or do we need a Stripe credit-line? Defer to billing-tier code; the migration adds the column, the planner decides whether to wire Stripe.
3. **Worker domain support detection.** Today workers don't advertise domain support — they take whatever the GA throws at them. The claim payload's `domains_supported` is forward-looking; for v1 send `["all"]` from every worker and skip the filter.
4. **Steering observability frontend.** Admin page showing the last 20 steers + outcomes. Not required for v1; metrics dashboard covers ops.
5. **Researcher tier UI.** "Submit a conjecture" page and live progress view. Frontend work tracked separately under Phase 9 P-Task 10 + a new Researcher-tier task.

---

## Files touched (master inventory)

**New:**
- `engine/crates/llm/src/gradient.rs`
- `engine/crates/api/src/steerer/mod.rs`
- `engine/crates/api/src/steerer/cycle.rs`
- `engine/crates/api/src/steerer/demand.rs`
- `engine/crates/api/src/steerer/prompt.rs`
- `engine/crates/api/src/steerer/schema.rs`
- `engine/crates/api/src/handlers/steering.rs`
- `engine/crates/api/src/handlers/research_jobs.rs`
- `engine/crates/api/src/handlers/jobs_claim.rs`
- `engine/crates/api/src/jobs/lease.rs` (claim + heartbeat + reaper)
- `engine/crates/pg/src/entity/cluster_steering.rs`
- `engine/crates/pg/src/query/cluster_steering.rs`
- `engine/crates/pg/src/migrator/m20260501_000001_cluster_steering.rs`
- `engine/crates/pg/src/migrator/m20260501_000002_paid_job_quota.rs`
- `engine/crates/pg/src/migrator/m20260501_000003_research_credits.rs`

**Modified:**
- `engine/crates/llm/src/lib.rs` (register Gradient provider)
- `engine/crates/llm/src/registry.rs` (add `gradient` entry)
- `engine/crates/api/src/main.rs` (spawn steerer + reaper tasks; mount new routes)
- `engine/crates/api/src/handlers/seed.rs` (fold steering ETag into seed response)
- `engine/crates/api/src/handlers/conjecture.rs` (add quota fields to view)
- `engine/crates/api/src/state.rs` (steering ArcSwap, demand cache)
- `engine/crates/ga/src/bin/worker.rs` (claim loop, heartbeat, steering hot-reload)
- `engine/crates/ga/src/chain_engine.rs` (read mutation knobs from steering)
- `engine/crates/api/src/metrics.rs` (new gauges/counters)
- `engine/crates/pg/src/entity/conjecture_jobs.rs` (new columns)
- `engine/crates/pg/src/entity/users.rs` (research_credits column)

---

## End-to-end smoke

After all tasks land:

1. Boot the cluster fresh. Assert `cluster_steering` is empty, default config served at `/api/steering`. Assert Kimi reachable via `GET https://inference.do-ai.run/v1/models`.
2. Wait 10 min. Assert one `cluster_steering` row, ETag served, workers logged "steering reloaded".
3. Generate fake demand via 50 search hits across 3 domains. Wait one more cycle. Assert next config's `domain_weights` shifts toward the searched domains (Kimi sees the demand).
4. Submit a paid conjecture job via `POST /api/research/jobs`. Assert one row in `conjecture_jobs` state=queued, user's `research_credits` decremented by 1.
5. Worker claims. Heartbeat starts. SSE stream connected from a curl session. Assert events arrive every 30s.
6. Wait for next steerer cycle. Assert mode flipped to `B`. Assert config has no `mutation_knobs`.
7. Force a Lean-verified outcome (test hook). Assert SSE emits `proved`, .lean URL works, job state=proved.
8. Cancel a second job mid-flight. Assert worker drops slice, refund applied, `research_credits` back to 1.
