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

## Phase A.5 follow-ups (not yet wired)

- Worker GA loop integration: feature-flag-guarded calls into `verify_with_cache`
  from `discover_emc2.rs` and the verification worker pool.
- Persistent-Lean Lean-side script: today the script is a `Ping`-only stub;
  full elaboration loop is owned by the prover team.
- `Fatal` response → drain inflight: when `PersistentElaborator`'s reader
  task sees `Fatal`, currently it logs but doesn't release pending oneshots;
  callers wait `request_timeout` (30s default).
