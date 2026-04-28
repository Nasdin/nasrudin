# LLM-Guided Search + Caching Layer — Design

**Date:** 2026-04-28
**Status:** Draft, awaiting review
**Scope:** New researcher-facing capability (`/conjecture`) + cross-cutting performance work (persistent Lean, attempts cache, tactic priors).

---

## 1. Overview

Today the platform brute-forces a GA over an axiom set, ships every survivor through Lean 4 verification, and accumulates a corpus. Throughput is bottlenecked by (a) Lean's per-attempt overhead and (b) the GA having no prior over which mutations are worth attempting. The corpus is *sound* — Lean filters that — but *yield* (interesting verified theorems per CPU-hour) is low and there is no way for a researcher to direct the search.

This spec adds two layers:

- **A. LLM-guided search** — a researcher-facing surface where an English conjecture turns into a guided GA run on the distributed worker fleet. LLM is server-side only; one call per conjecture; result is a "guided seed" (axiom subset + initial population + mutation priors) that workers execute.
- **B. Caching layer** — three throughput optimisations that benefit every worker (background corpus-fill *and* research jobs): persistent Lean elaborator, RocksDB attempts memoisation, RocksDB tactic-priors.

Both layers ship together. Workers carry no LLM keys; all LLM I/O is server-side.

### Architectural decisions, locked

| Decision | Choice |
|---|---|
| Conjecture loop shape | **γ** — sync LLM phase, human-in-loop checkpoint, async GA phase with SSE progress |
| LLM placement | **X** — server-side only, one call per conjecture, workers run regular GA on the LLM's seed |
| Worker job dispatch | **Q** — distributed research queue; workers opt into "research mode" |
| Scope | **Full A + Full B** — no thin slices |

---

## 2. Top-level architecture

```
                 ┌─────────────────────────────────────────────┐
                 │          Researcher's browser               │
                 │  /conjecture page · /settings · /jobs/:id   │
                 └────────────┬────────────────────────────────┘
                              │ HTTPS + SSE
                              ▼
   ┌────────────────────────────────────────────────────────────┐
   │                  Axum API server                            │
   │  POST /api/conjecture       POST /api/me/llm-keys           │
   │  GET  /api/conjecture/{id}  DEL  /api/me/llm-keys/{p}       │
   │  GET  /api/conjecture/{id}/sse                              │
   │       ▲                                                     │
   │       │ orchestrates                                        │
   │       ▼                                                     │
   │  ┌──────────────────┐  ┌───────────────────────────────┐    │
   │  │ nasrudin-llm     │  │ conjecture module (api crate) │    │
   │  │  (new crate)     │  │  job lifecycle, SSE fan-out   │    │
   │  │  Provider trait  │  └──────────────┬────────────────┘    │
   │  │  Anthropic impl  │                 │                     │
   │  │  OpenAI impl     │                 ▼                     │
   │  │  Ollama impl     │  ┌───────────────────────────────┐    │
   │  │  encrypted keys  │  │ nasrudin-embed (new crate)    │    │
   │  └──────────────────┘  │  fastembed (gte-small, 384d)  │    │
   │                        │  corpus index (mmap)          │    │
   │                        └───────────────────────────────┘    │
   └─────────────────────────────────┬───────────────────────────┘
                                     │
                       Postgres: conjecture_jobs queue
                                     │
                                     ▼
   ┌────────────────────────────────────────────────────────────┐
   │  Research-mode worker  (existing worker binary, new flag)   │
   │   POST /api/conjecture/claim                                │
   │   POST /api/conjecture/{id}/submit                          │
   │   POST /api/conjecture/{id}/heartbeat                       │
   │                                                             │
   │   In-process pieces (cache layer B, every worker):          │
   │    • PersistentLeanElaborator (long-lived lean --server)    │
   │    • AttemptsCache  (RocksDB CF, hash → outcome, TTL 30d)   │
   │    • TacticPriors   (RocksDB CF, goal_skel → chain, hits)   │
   │    • EmbeddingIndex (read-only mmap of server-built corpus) │
   └────────────────────────────────────────────────────────────┘
```

**New crates:**
- `engine/crates/llm/` — `nasrudin-llm`: provider trait + impls + key encryption
- `engine/crates/embed/` — `nasrudin-embed`: corpus embedding builder + retrieval

**New module inside existing crate:**
- `engine/crates/api/src/handlers/conjecture.rs` + `engine/crates/api/src/conjecture/` (job state machine, SSE fan-out)

**New Postgres table:** `conjecture_jobs`

**New RocksDB column families** (on every node that has a RocksDB instance — server + workers):
- `attempts` — `(canonical_hash || axiom_set_hash) → outcome_record`
- `tactic_priors` — `(goal_skeleton_hash || axiom_set_hash) → tactic_chain_record`

---

## 3. Cache layer (B)

Three independent caches. Each can ship and be measured separately. All live on the worker side; the server's in-process GA (used for E=mc² seed runs today) gets them too because it shares the same engine crates.

### 3.1 Persistent Lean elaborator

**Today:** every Lean verification spawns a new process or invokes lean inline; either way Mathlib's symbol table (~250 MB compressed olean) is reloaded per call.

**Change:** introduce `nasrudin_derive::lean::PersistentElaborator`, a wrapper around a long-lived `lean --server` subprocess speaking JSON-RPC. Workers hold one per CPU thread (or one shared, with a queue — TBD by benchmarking; default to one shared with mpsc).

- Process pre-loads `import Mathlib` once at boot (~3-8 s startup).
- Subsequent type-check / proof-attempt requests round-trip in 5-50 ms vs. current 200-2000 ms.
- Health check: if the process dies, replace it; if a request times out (configurable, default 30 s), kill the process and retry on a fresh one (Lean state can corrupt on bad input).
- Every batch of N requests, also re-import the latest catalog axioms so newly-published theorems are visible without restart.

**Where it integrates:** replaces the path A (in-process) call in the existing reverify pipeline + the worker GA's verification step. Path B (subprocess `lake build` per file) stays as a fallback for batches > 100 candidates or for the public re-verify-locally story. Both paths exist after this change.

### 3.2 Attempts cache

**Today:** if Worker-1 attempts expression X and Lean rejects it, Worker-2 attempting expression X next week pays the same Lean cost.

**Change:** RocksDB column family `attempts`, keyed by `(canonical_hash, axiom_set_hash)`, value = `AttemptRecord`:

```rust
pub struct AttemptRecord {
    pub outcome: AttemptOutcome,         // Accepted | RejectedTypeError | RejectedTimeout | RejectedTautology
    pub lean_version: String,            // for invalidation when Lean upgrades
    pub timestamp: DateTime<Utc>,
    pub attempted_by: String,            // worker_id
    pub elapsed_ms: u32,
}
pub enum AttemptOutcome {
    Verified { theorem_id: [u8; 8], tactic: String },
    RejectedTypeError { msg: String },   // truncated to 256 bytes
    RejectedTimeout,
    RejectedTrivial { reason: String },  // tautology, already-in-mathlib match, etc.
    Pending,                              // currently being attempted (with lease ttl)
}
```

- TTL: 30 days (configurable). After expiry the entry is recomputed on next attempt — handles upstream Mathlib changes.
- Key encoding: `canonical_hash` is already 8 bytes (`Theorem.canonical_hash`). `axiom_set_hash` is a new 8-byte BLAKE3 over the sorted list of axiom IDs in scope when the attempt is made.
- Integration point: `verify_candidate(expr)` becomes `attempts_cache.lookup_or_compute(expr, |e| verify(e))`. Cache lookups are ~1 µs (RocksDB block cache); cache misses fall through to actual verification.
- Invalidation: bumping `engine_git_sha` or `lean_version` invalidates everything (separate KV tracking last-known versions).

### 3.3 Tactic priors

**Today:** the verifier tries 8 tactics in fixed order: `simp` → `ring` → `linarith` → `nlinarith` → `polyrith` → `positivity` → `decide` → `norm_num`. ~80% of successful proofs win on the first 2; the rest of the cascade is wasted on most goals.

**Change:** RocksDB column family `tactic_priors`, keyed by `(goal_skeleton_hash, axiom_set_hash)`. Value:

```rust
pub struct TacticPriorRecord {
    pub successes: Vec<TacticSuccess>,   // sorted by hit count desc
    pub last_updated: DateTime<Utc>,
}
pub struct TacticSuccess {
    pub tactic_chain: String,            // e.g. "simp [add_comm, mul_comm]; ring"
    pub hits: u32,
    pub avg_elapsed_ms: u16,
}
```

- `goal_skeleton_hash` = BLAKE3 over the canonical form of the goal with all *literal numerals* and *fresh variable names* erased (e.g. `forall (a b : ℝ), a*b = b*a` and `forall (x y : ℝ), x*y = y*x` hash the same). Computed by an `Expr → skeleton` function in `nasrudin-core` (new module).
- On verification: try the top-3 cached tactic chains for this goal skeleton first; only fall back to the full 8-tactic cascade if none succeed.
- On success: increment hit count for the winning tactic chain; insert if new.
- TTL: none. Tactic priors only get better over time. Bounded by number of distinct goal skeletons (estimated < 10⁵ in steady state).

### 3.4 Cache layer integration plan

Caches are introduced one at a time, each gated by a feature flag (`NASRUDIN_CACHE_ATTEMPTS=1`, etc.) so each can be A/B'd against baseline before being made the default. A `nasrudin worker stats` subcommand reports cache hit rates.

---

## 4. LLM router crate (`nasrudin-llm`)

New crate at `engine/crates/llm/`. No `unsafe`, no `tokio::spawn` of unbounded tasks, all I/O timeouts ≤ 60 s.

### 4.1 Public API

```rust
#[async_trait]
pub trait LlmProvider: Send + Sync {
    fn name(&self) -> &'static str;             // "anthropic" | "openai" | "ollama"
    fn supported_models(&self) -> &[&'static str];

    /// Single-shot completion. Used for the conjecture LLM call.
    async fn complete(&self, req: CompletionRequest) -> Result<CompletionResponse>;

    /// Streaming completion. Used for paper-draft generation.
    async fn stream<'a>(&'a self, req: CompletionRequest)
        -> Result<BoxStream<'a, Result<TokenChunk>>>;
}

pub struct CompletionRequest {
    pub model: String,
    pub system_prompt: String,
    pub user_prompt: String,
    pub max_tokens: u32,
    pub temperature: f32,
    pub stop_sequences: Vec<String>,
    pub response_format: ResponseFormat,      // Free | Json(schema)
}
```

### 4.2 Provider implementations (all first-class)

- `anthropic.rs` — Messages API, supports Claude Sonnet 4.6 / Opus 4.7 / Haiku 4.5.
- `openai.rs` — Chat Completions API, supports GPT-4o / GPT-4o-mini / o1.
- `ollama.rs` — local HTTP at `http://localhost:11434`, supports any installed model. Useful for institute-internal runs without paying per token.

Each impl handles its own retries (exponential backoff, max 3), rate-limit headers, and error normalisation into `LlmError`.

### 4.3 BYO API keys

Per-user, encrypted at rest. New Postgres table:

```sql
CREATE TABLE user_llm_keys (
    user_id        UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    provider       TEXT NOT NULL,                 -- 'anthropic' | 'openai' | 'ollama'
    encrypted_key  BYTEA NOT NULL,                -- AES-256-GCM, key from env NASRUDIN_KEY_ENCRYPT
    key_hint       TEXT NOT NULL,                 -- last 4 chars only, for UI display
    created_at     TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    last_used_at   TIMESTAMPTZ,
    PRIMARY KEY (user_id, provider)
);
```

Encryption: AES-256-GCM with the server's `NASRUDIN_KEY_ENCRYPT` (32 bytes, base64-encoded in env). Nonce = random 12 bytes prepended to ciphertext. The key never leaves the server. The plaintext is decrypted in-process only when calling the LLM provider; never logged, never returned to the client.

API endpoints:

| Method | Path | Auth | Purpose |
|---|---|---|---|
| `GET` | `/api/me/llm-keys` | cookie | list user's providers + key hints (no plaintext) |
| `POST` | `/api/me/llm-keys` | cookie | save a key for a provider (body: `{ provider, key }`) |
| `DELETE` | `/api/me/llm-keys/:provider` | cookie | revoke a provider's key |

### 4.4 Provider selection

Each conjecture request specifies `provider` and `model`. If the user has no key for the chosen provider, return 400 `no_provider_key`. If the request omits provider, use the user's default (stored in `user_preferences.preferences.llm.default_provider`).

---

## 5. Embedding store (`nasrudin-embed`)

New crate at `engine/crates/embed/`. Used by the LLM router to retrieve nearest-corpus matches for a conjecture, and by the GA tactic-priors lookup (goal-skeleton embeddings as a fallback when exact hash misses).

### 5.1 Model

Local CPU model via `fastembed-rs` (Rust binding for ONNX). Default: **`BAAI/bge-small-en-v1.5`** (384 dimensions, ~130 MB, ~2 ms / query on a single CPU core). Pure Rust, no Python sidecar.

### 5.2 Corpus index

- Built server-side once nightly (cron) and after every batch of N=1000 newly-verified theorems.
- Source: every verified theorem's `canonical_statement` + `name` + `domain` concatenated.
- Output: a flat memory-mapped file `corpus.embed` in `~/.nasrudin/embed/` containing `{theorem_id, vector}` pairs, plus a sidecar HNSW index (via `instant-distance` crate).
- Distributed to workers as a static asset alongside the worker binary release; workers mmap it read-only. Updated workers pull the latest on heartbeat.
- Size estimate: 250k theorems × (8 bytes id + 384 × 4 bytes vector) = ~390 MB on disk per snapshot. Well within the 2 GB worker budget.

### 5.3 Public API

```rust
pub struct EmbeddingIndex { /* ... */ }
impl EmbeddingIndex {
    pub fn open(path: &Path) -> Result<Self>;
    pub fn embed(&self, text: &str) -> Result<Vec<f32>>;        // 384-dim
    pub fn nearest(&self, vec: &[f32], k: usize) -> Vec<(TheoremId, f32)>;
    pub fn nearest_text(&self, text: &str, k: usize) -> Result<Vec<(TheoremId, f32)>>;
}
```

The conjecture module calls `nearest_text(hunch, 10)` to retrieve the seed neighbours that get fed to the LLM.

---

## 6. Conjecture loop (γ)

State machine for a `conjecture_jobs` row:

```
                     │ POST /api/conjecture
                     ▼
                 ┌─────────┐
                 │ Created │
                 └────┬────┘
                      │ server runs LLM phase (≤ 60 s budget)
                      ▼
              ┌──────────────────┐
              │ LlmComplete      │   ← researcher inspects suggestions, picks one,
              │ (suggestions     │     edits axiom subset / budget, hits "run"
              │  available)      │     OR auto-advance after 5 min if user idle
              └────────┬─────────┘
                       │ POST /api/conjecture/{id}/start
                       ▼
              ┌──────────────────┐
              │ QueuedForWorker  │   ← row visible to research-mode workers
              └────────┬─────────┘
                       │ worker claims (lease, 5 min ttl)
                       ▼
              ┌──────────────────┐
              │ Running          │   ← workers heartbeat, submit candidates
              └────────┬─────────┘
                       │ budget exhausted | candidate verified | timeout | cancel
                       ▼
              ┌──────────────────┐
              │ Complete         │   (Verified | NoResult | TimedOut | Cancelled)
              └──────────────────┘
```

### 6.1 `POST /api/conjecture` (cookie auth)

Request:

```json
{
  "hunch": "Energy and mass should relate via the speed of light squared",
  "domain_hint": "SpecialRelativity",
  "provider": "anthropic",
  "model": "claude-sonnet-4-6",
  "budget": { "wall_seconds": 600, "max_candidates": 100000 }
}
```

Server flow (synchronous, ≤ 60 s):

1. Insert row `conjecture_jobs(state=Created, hunch, owner_id, ...)`.
2. `EmbeddingIndex::nearest_text(hunch, 10)` — get top corpus matches.
3. Build LLM prompt (system + user) with hunch + neighbours + axiom catalog summary.
4. Call `LlmProvider::complete()` requesting JSON output (response_format = Json(schema)).
5. Parse the LLM's response into `LlmSuggestion[]`:
   ```rust
   pub struct LlmSuggestion {
       pub axiom_set: Vec<String>,           // axiom IDs to enable
       pub initial_population: Vec<Expr>,    // 5-10 seed expressions
       pub mutation_priors: HashMap<String, f32>,  // operator → weight
       pub target_shape: Option<String>,     // free-form description for the researcher
       pub rationale: String,                // why these seeds
   }
   ```
6. Update row: `state=LlmComplete, suggestions=<json array>`.
7. Return `{ job_id, suggestions }` — researcher sees them.

### 6.2 `POST /api/conjecture/{id}/start` (cookie auth)

Body: `{ chosen_suggestion_index, budget_overrides? }`. Transitions row from `LlmComplete` → `QueuedForWorker`. Workers poll `/api/conjecture/claim` and pick it up.

### 6.3 `GET /api/conjecture/{id}/sse`

Server-Sent Events stream. Events:

- `state_change` — `{ from, to, at }`
- `candidate_verified` — `{ theorem_id, statement_latex, tactic, elapsed_ms, worker_id }`
- `progress` — `{ candidates_attempted, candidates_verified, time_elapsed_s, time_remaining_s }`
- `complete` — `{ outcome, theorem_ids, paper_draft_url? }`

Server multiplexes events from multiple workers on the same job into the SSE stream by tailing a Postgres-backed event log table `conjecture_events`.

### 6.4 LLM prompt template

System prompt (pinned, version-tracked):

```
You are an assistant for a formal-theorem-discovery system. Given a researcher's
informal conjecture and a set of related verified theorems from the existing
corpus, produce a JSON array of derivation seeds the system can search from.

Each seed includes:
- axiom_set: which axioms to enable (subset of the provided catalog)
- initial_population: 5-10 expression sketches the GA should mutate
- mutation_priors: per-operator weights biasing the GA's mutation choices
- target_shape: optional human-readable description of the target form

You DO NOT prove anything. You suggest where to search.
```

User prompt: hunch + nearest 10 corpus matches (id, statement, domain) + axiom catalog (compressed: id + statement only).

Token budget: ~8k input, ~4k output. Per-call cost on Sonnet 4.6: ~$0.05.

---

## 7. Research-queue worker pool (Q)

### 7.1 New table `conjecture_jobs`

```sql
CREATE TABLE conjecture_jobs (
    id              UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    owner_id        UUID NOT NULL REFERENCES users(id),
    state           TEXT NOT NULL,             -- Created|LlmComplete|QueuedForWorker|Running|Complete
    outcome         TEXT,                       -- Verified|NoResult|TimedOut|Cancelled (when Complete)

    hunch           TEXT NOT NULL,
    domain_hint     TEXT,
    provider        TEXT NOT NULL,
    model           TEXT NOT NULL,

    suggestions     JSONB,                      -- LlmSuggestion[], filled at LlmComplete
    chosen_index    INT,                        -- which suggestion the researcher picked
    seed            JSONB,                      -- final seed packaged for the worker
    budget          JSONB NOT NULL,             -- { wall_seconds, max_candidates }

    claimed_by      TEXT,                       -- workers.id when leased
    claimed_at      TIMESTAMPTZ,
    lease_expires_at TIMESTAMPTZ,
    last_heartbeat_at TIMESTAMPTZ,

    candidates_attempted INT NOT NULL DEFAULT 0,
    candidates_verified  INT NOT NULL DEFAULT 0,
    verified_theorem_ids BYTEA[],               -- 8-byte each

    created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    completed_at    TIMESTAMPTZ
);
CREATE INDEX idx_conjecture_jobs_queueable
  ON conjecture_jobs (created_at)
  WHERE state = 'QueuedForWorker' AND claimed_by IS NULL;
CREATE INDEX idx_conjecture_jobs_owner
  ON conjecture_jobs (owner_id, created_at DESC);
```

And an event-log table:

```sql
CREATE TABLE conjecture_events (
    id          BIGSERIAL PRIMARY KEY,
    job_id      UUID NOT NULL REFERENCES conjecture_jobs(id) ON DELETE CASCADE,
    kind        TEXT NOT NULL,                  -- state_change|candidate_verified|progress
    payload     JSONB NOT NULL,
    at          TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX idx_conjecture_events_job ON conjecture_events (job_id, id);
```

### 7.2 Worker endpoints (Bearer `nsk_worker_…`, research mode required)

`POST /api/conjecture/claim`

- Worker must be in research mode (config flag set + heartbeat reflects it).
- Atomic: `UPDATE conjecture_jobs SET claimed_by=$1, claimed_at=NOW(), lease_expires_at=NOW()+'5 min', state='Running' WHERE id = (SELECT id FROM conjecture_jobs WHERE state='QueuedForWorker' AND claimed_by IS NULL ORDER BY created_at LIMIT 1 FOR UPDATE SKIP LOCKED) RETURNING ...`.
- Returns `{ job_id, seed, budget }` or 204 if nothing queued.

`POST /api/conjecture/{id}/heartbeat`

- Body: `{ candidates_attempted, candidates_verified, time_elapsed_s }`.
- Updates `last_heartbeat_at`, extends `lease_expires_at`, updates progress counters.
- Inserts a `progress` event into `conjecture_events`.

`POST /api/conjecture/{id}/submit`

- Body: `{ theorem: TheoremIngest }` — same shape as existing `/api/ingest`, just routed differently.
- Server re-verifies via the existing path; on success, append theorem id to `verified_theorem_ids`, insert `candidate_verified` event.

`POST /api/conjecture/{id}/complete`

- Body: `{ outcome, reason }`. Worker calls when budget exhausted or target hit.
- Transitions row to `state='Complete'`, sets `completed_at`, emits final `complete` event.

### 7.3 Lease reaper

Background task on the server (started in main.rs alongside the GA pool): every 30 s, query for `lease_expires_at < NOW() AND state='Running'`, set `claimed_by=NULL, state='QueuedForWorker'`. Re-queues jobs from dead workers.

### 7.4 Worker mode flag

Workers gain `--research-mode` flag (and `NASRUDIN_RESEARCH_MODE=1` env). Defaults to off — the existing fleet keeps doing background corpus-fill. Setting the flag enables: heartbeat advertises it, claim loop polls `/api/conjecture/claim` between background batches.

A worker config can be `--research-mode-only` (skip background work entirely) or `--research-mode-share=0.5` (devote 50 % of CPU time to research jobs).

---

## 8. Frontend

### 8.1 New routes

- `/conjecture` — paste hunch + provider/model dropdowns + budget slider + submit.
- `/conjecture/$id` — live job view, SSE-driven. Sections: hunch, LLM suggestions (with edit/select before "start"), running progress (when claimed), final results.
- `/jobs` — list of all the user's conjecture jobs with status pills.

### 8.2 Settings additions

In the existing `/settings` page, new "LLM providers" section. For each provider (Anthropic, OpenAI, Ollama):

- "Add key" → modal with paste field + provider description.
- Existing key → shown as `Anthropic · ····xR4q  ✓ used 3 hours ago` with a Revoke button.
- Default-provider radio.

### 8.3 New hooks (`lib/queries.ts`)

```ts
useLlmKeys()                         // GET /api/me/llm-keys
useSetLlmKey()                       // POST /api/me/llm-keys
useRevokeLlmKey()                    // DELETE /api/me/llm-keys/:provider
useCreateConjecture()                // POST /api/conjecture
useConjecture(id)                    // GET /api/conjecture/:id
useStartConjecture(id)               // POST /api/conjecture/:id/start
useConjectureStream(id)              // EventSource → /api/conjecture/:id/sse
useMyConjectures()                   // GET /api/me/conjectures
```

### 8.4 AppHeader / nav

Add `/conjecture` to the subnav between `/library` and `/workers`. Highlight active.

---

## 9. Paper draft generation (stretch, in-scope)

When a conjecture's GA verifies a theorem, an optional paper-draft pass:

- Server collects: the verified theorem (statement + Lean proof + lineage), the original hunch, the LLM's rationale, the GA's mutation history.
- Calls the same LLM provider once more (`stream` mode this time) with a "write a 1-2 page paper draft in Markdown" prompt.
- Streams the draft back through the SSE channel as `paper_chunk` events.
- Final draft URL: `/api/conjecture/{id}/paper.md` (also browsable in the UI).

The user can edit the draft (in-browser textarea), save it, and download as `.md` or `.tex`. Integrated citations to corpus theorems via existing `/api/theorems/:id` URLs.

---

## 10. Error handling & observability

- All LLM calls timeout at 60 s; on failure, job transitions to `Complete{outcome=Failed, reason}`. Researcher can retry.
- All worker endpoints validate authentication, research-mode flag, and lease ownership; mismatches return `403`.
- Lease expires → reaper requeues; researcher sees `progress` event with `worker_lost: true`.
- Per-provider rate limiting (token-bucket per user, configurable in `nasrudin-llm`).
- Tracing: each conjecture job tagged with a trace id propagated to all worker calls; spans emitted via `tracing` crate, exported to optional OpenTelemetry collector.
- Metrics: conjecture-job throughput, LLM cost per job, cache hit rates (each cache layer reports separately), worker research-mode utilisation.

---

## 11. Testing strategy

| Layer | Tests |
|---|---|
| `nasrudin-llm` provider impls | One mocked HTTP server per provider, integration tests round-trip a fixture conjecture and assert structured output parses. |
| `nasrudin-embed` | Determinism test (same text → same vector), sanity test (semantically related theorems are nearer than unrelated). |
| Cache CFs | Property tests: (a) write-then-read invariants, (b) TTL semantics, (c) crash-resilience via `rocksdb::checkpoint`. |
| Persistent Lean | Soak test: 10k consecutive type-checks against a single elaborator, verify no leak / no slowdown. |
| Conjecture loop | End-to-end test using a stub LLM provider and a single in-process worker; asserts state machine reaches Complete with the expected theorem id. |
| Frontend | Component tests for `/conjecture` form, integration test for the SSE flow against a mock server. |

The existing nightly integration test (`e2e_spontaneous_emc2_ingest`) gets a sibling: `e2e_conjecture_emc2`, where the hunch text is the E=mc² conjecture in English, and the test asserts the GA verifies the canonical E=mc² theorem within the budget.

---

## 12. Out of scope (explicit non-goals)

- **Worker-side LLM calls (option Z).** Reconsider once X-mode metrics show the LLM seed is good but the GA loop wastes cycles inside one run; until then, no API keys leave the server.
- **Multi-tenant cost limits.** Researchers pay for their own LLM via BYO key, so the platform doesn't need its own cost ceilings; revisit if a free tier ever ships.
- **Federated research-mode workers across organisations.** All workers in v1 belong to one trust domain (the platform). Cross-org research jobs need a separate trust model.
- **Paper auto-submission to arXiv.** The draft is generated; submission stays manual.

---

## 13. Migration & rollout

1. **Phase A — caches under feature flags.** Land `attempts` CF + `tactic_priors` CF + `PersistentElaborator` behind env flags, off by default. Soak on the dev box for a week.
2. **Phase B — embed crate + nightly index build.** Index ships to workers via a new `/api/embed/index.bin` endpoint (signed checksum). Workers download on next heartbeat.
3. **Phase C — LLM crate + key endpoints + settings UI.** No conjecture flow yet; users can save keys but nothing consumes them.
4. **Phase D — `conjecture` module + `/conjecture` endpoints + frontend route.** Launch with `provider=anthropic` only; add OpenAI + Ollama in a follow-up.
5. **Phase E — research-mode worker flag + claim/heartbeat/submit.** Soft launch: a single dev worker in research mode picks up jobs.
6. **Phase F — paper draft generation, then announce publicly.**

Each phase ships independently behind flags; no coordinated big-bang deploy.

---

## 14. Open questions for the implementation plan

- Exact tactic-skeleton hash function (which `Expr` features survive normalisation?). Likely settled during plan writing.
- Whether the `PersistentElaborator` should run one process or one-per-thread for path A. Benchmark in plan.
- Default budget shape — wall seconds vs candidate count vs both. Default to both with `min(wall, candidates)` semantics.
- Whether to ship Anthropic-first and add OpenAI/Ollama incrementally, or all three at once. Default to all three given the "infinite resources" framing.

---

*End of design.*
