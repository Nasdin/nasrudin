# Conjecture loop (Phase D)

Phase D wires the **server-side LLM call** + **`conjecture_jobs` state machine**.
The dequeue side (research-mode worker claim/heartbeat/submit) lands in Phase E.

## State machine

```
Created → LlmComplete → QueuedForWorker → (Phase E: Running → Complete)
                              ↑
                       set_chosen_seed
```

A failure during the LLM phase short-circuits to
`Complete{outcome=Failed:<reason>}` and surfaces immediately.

## Endpoints

| Verb | Path | Notes |
|---|---|---|
| `POST`   | `/api/conjecture`              | Sync; runs the LLM; returns suggestions |
| `POST`   | `/api/conjecture/{id}/start`   | Picks a suggestion → `QueuedForWorker` |
| `GET`    | `/api/conjecture/{id}`         | Full row (suggestions + seed + progress) |
| `GET`    | `/api/conjecture/{id}/sse`     | History replay then live broadcast |
| `GET`    | `/api/me/conjectures`          | List the caller's last 50 jobs |

All five require cookie auth (or `Bearer nsk_live_…`) and return 503 if
`NASRUDIN_KEY_ENCRYPT` is unset (the LLM call can't decrypt).

## Provider scope

Phase D launches **anthropic only** per spec §13. Other providers get
`400 unsupported_provider`. OpenAI + Ollama already wire through
`nasrudin_llm`'s `Registry`; the launch flag lives in
`handlers/conjecture.rs::create` — drop the check to enable.

## SSE wire format

Each `Event` carries:

- `event` — `state_change | progress | candidate_verified | complete`
- `data`  — JSON `{ id, kind, payload, at }`

History (everything in `conjecture_events` for the job, ascending `id`)
is replayed first, then the in-process `broadcast::Sender<ConjectureEvent>`
is subscribed and filtered by `job_id`. Keep-alive pings every 15 s.

## What Phase D does NOT do

- Worker dequeue. The row sits in `QueuedForWorker` until Phase E ships
  `/api/conjecture/claim` + heartbeat + submit.
- Embedding-driven retrieval. `nearest_neighbours` returns `Vec::new()`
  until a fastembed `Embedder` is threaded into `AppState` — separate task.
  The LLM still receives the axiom catalog, which is enough for useful seeds.
- Paper draft generation (Phase F).

## Testing

Unit:

```bash
cargo test -p physics-api conjecture::types::tests --lib
cargo test -p physics-api conjecture::prompt --lib
```

Auth-gate smokes:

```bash
cargo test -p physics-api --test conjecture_handler
```

The full end-to-end E=mc² nightly (`e2e_conjecture_emc2`) lands once Phase E
ships the worker side.

## Phase E (worker side)

Phase E adds the dequeue half. Workers run with `--research-mode`
(or `NASRUDIN_RESEARCH_MODE=1`) and call:

| Verb   | Path                                  | Purpose |
|--------|---------------------------------------|---------|
| `POST` | `/api/conjecture/claim`               | Atomic dequeue (`FOR UPDATE SKIP LOCKED`). 5-min lease. |
| `POST` | `/api/conjecture/{id}/heartbeat`      | Extend lease + report progress. |
| `POST` | `/api/conjecture/{id}/submit`         | One verified theorem (delegates to ingest path). |
| `POST` | `/api/conjecture/{id}/complete`       | Final transition (Verified / NoResult / TimedOut / Cancelled). |

All four require `Authorization: Bearer nsk_worker_…` (`WorkerAuth`)
and pass through the per-worker rate limiter.

### Lease + reaper

- Each claim sets `lease_expires_at = NOW() + 5 minutes`.
- Heartbeat extends the lease another 5 minutes.
- The `ConjectureLeaseReaper` background task ticks every 30 s,
  requeues `state='Running' AND lease_expires_at < NOW()` rows,
  and emits `progress {worker_lost: true}` for SSE subscribers.

### Seed-driven GA

When a worker claims a job, `run_seed_driven_chunk`:

1. Parses the `seed: serde_json::Value` into an `LlmSuggestion`.
2. Builds a *filtered* `AxiomStore`:
   - Always layers `classical_mechanics_postulates` as a kinematic baseline.
   - Adds each named axiom from `axiom_set` (warns on unknown names).
   - Registers each parseable string in `initial_population` as a
     `seed_<idx>` synthetic axiom so `IntroduceAxiom` picks it up.
3. Translates `mutation_priors` (operator → weight) into
   `DiscoveryConfig.mutation_priors`; `chain_ga::mutate_chain_weighted`
   then samples operators by the LLM's bias rather than uniform 1/6.
4. Runs in chunked iterations (≤30 s + 25 generations each) until
   the budget's `wall_seconds` or `max_candidates` is exhausted.
   Between chunks: heartbeat + submit each verified theorem to
   `/api/conjecture/{id}/submit`.
5. Calls `complete` with `outcome=Verified` (≥1 submitted) or
   `outcome=NoResult`, with a reason payload carrying the counters.

### Manual smoke

```bash
NASRUDIN_RESEARCH_MODE=1 \
NASRUDIN_API_URL=http://localhost:8080 \
NASRUDIN_WORKER_KEY=nsk_worker_… \
NASRUDIN_WORKER_ID=research-1 \
cargo run -p nasrudin-ga --bin worker -- --verify ../prover
```

The worker prints `claimed conjecture <uuid>` for every dequeued job
and `conjecture <uuid> → Verified|NoResult …` after the lease completes.

### Tests

```bash
cargo test -p nasrudin-pg --test conjecture_jobs_query  # 8 lifecycle tests
cargo test -p physics-api --test conjecture_worker      # 4 auth-gate smokes
```

## Phase F (paper draft generation)

Once a conjecture finishes with `outcome=Verified`, the researcher can
generate a Markdown paper draft summarising the discovery. The same LLM
provider that proposed the conjecture writes it.

| Verb   | Path                                  | Purpose |
|--------|---------------------------------------|---------|
| `POST` | `/api/conjecture/{id}/paper`          | Trigger background streaming. Returns 202 immediately. |
| `GET`  | `/api/conjecture/{id}/paper.md`       | Read the persisted draft as `text/markdown`. |

### Streaming wire format

The background task uses `LlmProvider::stream` (real implementation
landed for Anthropic in Phase F; OpenAI/Ollama remain stubbed). Each
`TokenChunk` is forwarded twice:
1. **Persisted** via `query::conjecture_jobs::append_paper_chunk` so the
   `paper_draft` column accumulates the full draft.
2. **Broadcast** as `paper_chunk` events on the existing conjecture SSE
   channel — the frontend reconstructs the live preview by concatenating
   them in arrival order.

Final transitions:
- `paper_done` event when `finish_reason` is set (clean end).
- `paper_error` event when the stream errors out (UI surfaces the message).

### Provider scope

- **Anthropic**: full SSE streaming against `/v1/messages` with
  `stream=true`. Parses `content_block_delta`, `message_stop`, `error`.
- **OpenAI / Ollama**: trait method exists but returns `LlmError::Other`.
  Phase F.1 will mirror the Anthropic implementation.

### Concept search (related, ships alongside Phase F)

`GET /api/search/concept?q=…` — natural-language search across the
corpus, hybrid embedding-nearest + Postgres ILIKE, surfaces both
verified theorems and pending conjectures so a user looking for
"all the equations that have to do with Energy" sees in-flight
work alongside completed proofs.
