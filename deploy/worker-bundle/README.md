# Nasrudin Discovery Worker

Distributed theorem-discovery worker for [nasrudin.org](https://nasrudin.org).
Runs a genetic-algorithm search over upstream physics axioms, lake-verifies
the survivors with Lean 4, and POSTs verified theorems to `api.nasrudin.org`.
Your discoveries land on the public catalog with your worker handle attributed.

## Quickstart

```bash
# 1. Install the Lean toolchain (one-time, ~200MB)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y

# 2. Get a worker key
#    Sign in at https://nasrudin.org -> /api-keys -> "+ New key" -> Kind: Worker
#    Save the `nsk_worker_…` value.

# 3. Run
NASRUDIN_API_URL=https://api.nasrudin.org \
NASRUDIN_WORKER_KEY=nsk_worker_xxxxxxxxxx \
./run.sh
```

`run.sh` wraps the binary with sensible defaults and points `--verify` at the
bundled `prover/` tree. First run will warm the Lean Mathlib cache (a few
minutes); subsequent runs reuse it.

## Configuration

| Environment variable    | Required | Default                     | Notes                                  |
|-------------------------|----------|-----------------------------|----------------------------------------|
| `NASRUDIN_WORKER_KEY`   | yes      | —                           | `nsk_worker_…` from `/api-keys`        |
| `NASRUDIN_API_URL`      | no       | `https://api.nasrudin.org`  | Override for self-hosted endpoints     |
| `NASRUDIN_WORKER_ID`    | no       | hostname                    | Identifier shown in the leaderboard    |

CLI flags (passed through `run.sh`, or run the binary directly):

```
./nasrudin-worker --help
  --gens N       generations to run        (default 100)
  --pop N        population size           (default 64)
  --max-len N    max chain length          (default 14)
  --max-lake N   verifications per gen     (default 12)
  --domain {sr,em}                         (default sr)
  --verify PATH  prover root for lake build (set by run.sh)
```

## What does it do?

Each generation:

1. Mutates a population of derivation chains over upstream physics axioms.
2. Lake-builds the top novel candidates (Lean 4).
3. Submits verified survivors to `/api/ingest` over HTTPS.
4. The platform de-dupes and re-verifies via its own pipeline (B-path),
   then broadcasts on `/api/events/discoveries` so peers can see your work
   and seed their own search from it.

Submitted theorems that already exist in the catalog return `Duplicate`
(harmless — your contributor counter doesn't double-count). Truly novel
results land as `Pending` and become `Verified` within a few seconds.

## Stopping

`Ctrl+C` is clean. Heartbeats stop, Postgres marks the worker stale after
the configured TTL.
