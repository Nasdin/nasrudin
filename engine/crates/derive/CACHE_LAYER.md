# Cache Layer (Phase A)

Three caches, all opt-in via env flags. Default off. Each can be enabled independently.

## Flags

| Env var | Effect |
|---|---|
| `NASRUDIN_CACHE_ATTEMPTS=1` | Memoise verification attempts in the `attempts` RocksDB CF. 30-day TTL. |
| `NASRUDIN_CACHE_TACTIC_PRIORS=1` | Try cached tactic chains before the default cascade. No TTL. |
| `NASRUDIN_CACHE_PERSISTENT_LEAN=1` | Use a long-lived `lean --server` process instead of subprocess-per-call. |

Truthy values: `1`, `true`, `yes` (case-insensitive). Anything else is off.

## Inspecting

```bash
cargo build -p physics-api --bin cache-stats
./engine/target/debug/cache-stats --rocks-path ./data/rocks
```

Reports per-CF row counts and outcome breakdowns. Useful for measuring hit
rate over a workload (run before, run a workload, run after, diff).

## Architecture

- **`attempts` CF** — `(canonical_hash || axiom_set_hash) → AttemptRecord`.
  Hit-or-compute wrapper at `nasrudin_rocks::attempts_cache::AttemptsCache::lookup_or_compute`.
  Production wrapper at `nasrudin_derive::lean_verify::verify_with_cache`.
- **`tactic_priors` CF** — `(skeleton_hash || axiom_set_hash) → TacticPriorRecord`.
  Read helper at `nasrudin_lean_bridge::tactic::priors_for`.
  Recorded via `TacticPriorsCache::record_success` (caller responsibility).
- **Persistent Lean** — `nasrudin_lean_bridge::PersistentElaborator`. Boots
  one `lean --run scripts/nasrudin_server.lean` subprocess that imports
  Mathlib once, then multiplexes JSON-RPC requests over stdin/stdout.

## Spec

Full design: `docs/superpowers/specs/2026-04-28-llm-guided-search-design.md` §3.
Implementation plan: `docs/superpowers/plans/2026-04-29-llm-guided-search-phase-a-caches.md`.

## Phase A.5 — Wiring (2026-04-29)

The Phase A caches are now wired into both the GA hot path and the
server's reverify queue. With `NASRUDIN_CACHE_ATTEMPTS=1`,
`NASRUDIN_CACHE_TACTIC_PRIORS=1`, and `NASRUDIN_CACHE_PERSISTENT_LEAN=1`
set on the API server, verification skips redundant `lake build` calls.

### Closed prep items

| Item | Status |
|---|---|
| `axiom_set_hash` + `axiom_id_from_name` in `nasrudin_core::axiom_set` | Done |
| `AttemptsCache::on_existing_db` (shared `Arc<DB>`) | Done |
| `TacticPriorsCache::on_existing_db` (shared `Arc<DB>`) | Done |
| `verify_with_cache` 8-arg → `VerifyWithCacheCtx` struct | Done |
| `PersistentElaborator` Fatal → drain inflight oneshots | Done |
| `record_success` production caller | Wired in `verify_chain_cached` |

### Wiring map

| Path | Site | Behaviour when flag is on |
|---|---|---|
| In-process / external GA | `nasrudin_ga::chain_engine::run_discovery` → `chain_ga::verify_chain_cached` | Skips `lake build` on attempts-cache hit; records `tactic_priors` on success |
| API reverify queue | `physics_api::reverify::ReverifyQueue::process_one` → `LakeBuilder::verify_cached` | Same skip semantics on the server-side regen + worker-submitted Lean paths |
| Persistent Lean | `nasrudin_lean_bridge::PersistentElaborator` | A-path verification reuses one long-lived process; Fatal drains all pending oneshots |

### Constructing `CacheCtx`

The API server builds a single `CacheCtx` at boot via
`physics_api::cache::CacheCtx::build(&db)`. It carries:

- `config: CacheConfig` — read from env at boot.
- `bundle: CacheBundle` — `Arc<AttemptsCache>` + `Arc<TacticPriorsCache>` + `Arc<CacheStats>` against `db.shared_db()`, plus `lean_version`, `worker_id`, `ttl_days`.

External workers build their own `CacheBundle` and pass it into
`DiscoveryConfig.cache_ctx`. `CacheBundle` is `Clone` (refcount bumps);
each verify call gets its own clone via `config.cache_ctx.as_ref()`.

### Reading stats

```bash
cargo run --release --bin cache_stats -- --db ./data/theorems.db
```

Reports per-CF row counts. Live `CacheStats` counters surface via the
existing `/api/stats` endpoint once `cache_ctx` is wired into the
handler (Phase A.6 if requested by ops).

### Disabling

Unset the env vars (or set to `0`/`false`/`no`). All call sites fall
back to direct verification with no behavioural drift.
