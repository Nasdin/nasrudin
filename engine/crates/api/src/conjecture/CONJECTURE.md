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
