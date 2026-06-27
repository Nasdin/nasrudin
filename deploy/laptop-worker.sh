#!/bin/bash
# Nasrudin discovery worker — laptop launcher.
#
# This box (24 GB) does the heavy Lean verification the 2 GB droplet can't:
# it derives chains from the curated physics axioms, verifies each against
# the local Mathlib build (warm prover/.lake), and submits ONLY genuinely
# kernel-checked theorems to the droplet API over TCP.
#
# Soundness invariants (do not loosen):
#   NASRUDIN_NO_LOCAL_LAKE=0  — verify locally before submitting
#   NASRUDIN_SUBMIT_TOP_K=0   — never submit an unverified candidate
#   NASRUDIN_WORKER_NO_CORPUS=1 — physics-only pool; the 194k cold-tier
#     would bypass the seed-sync plumbing filter and reintroduce junk.
#
# The bearer key lives in ~/.nasrudin/worker.env (chmod 600), sourced below.
# Run by the launchd agent com.nasrudin.worker (starts at login, keep-alive).
set -euo pipefail

REPO="/Volumes/CORSAIR/code/personal/nasrudin"
WORKER_BIN="$HOME/.nasrudin/bin/worker"
ENV_FILE="$HOME/.nasrudin/worker.env"

# elan/lake on PATH for the local verification path.
export PATH="$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"

# Secret bearer token (nsk_worker_…). Kept out of this file and the plist.
# shellcheck source=/dev/null
[ -f "$ENV_FILE" ] && . "$ENV_FILE"

export NASRUDIN_API_URL="${NASRUDIN_API_URL:-https://api.nasrudin.org}"
export NASRUDIN_WORKER_ID="${NASRUDIN_WORKER_ID:-nasdin-macbook}"
export PROVER_ROOT="$REPO/prover"
export NASRUDIN_NO_LOCAL_LAKE=0
export NASRUDIN_SUBMIT_TOP_K=0
export NASRUDIN_WORKER_NO_CORPUS=1
# Persistent in-process elaborator: pay the one-time Mathlib import, then
# verify each candidate in <1s for the life of this worker instance. With
# 24 GB RAM the daemon stays resident (unlike the swap-thrashed droplet).
export NASRUDIN_NO_PERSISTENT=0

# The prover dir lives on an external volume; wait for it to mount at login.
for _ in $(seq 1 60); do
  [ -d "$PROVER_ROOT/.lake" ] && break
  sleep 5
done

# --chunks 8: keep one worker instance alive across many chunks so the
# elaborator's import cost amortizes (a --chunks 1 worker would re-import
# Mathlib on every launchd restart).
exec "$WORKER_BIN" --verify "$PROVER_ROOT" --domain sr --chunks 8 --max-lake 6
