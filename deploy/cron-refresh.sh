#!/usr/bin/env bash
# Weekly PhysLean + Mathlib refresh — pulls upstream, re-extracts the
# corpus, hot-reloads the live API. Add to crontab:
#   0 3 * * 0 /opt/physics-generator/deploy/cron-refresh.sh
#
# Required env (sourced from $PROJECT_DIR/.env if present):
#   ADMIN_TOKEN  — bearer token matching the API process's ADMIN_TOKEN
#   API_URL      — defaults to http://localhost:3001 if unset
set -euo pipefail
PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_DIR"

# Source .env if present so cron picks up ADMIN_TOKEN/API_URL without
# needing them in the systemd unit.
if [[ -f .env ]]; then
  set -a; source .env; set +a
fi
: "${API_URL:=http://localhost:3001}"

LOG="logs/refresh-$(date +%Y%m%d).log"
mkdir -p logs

{
  echo "=== PhysLean+Mathlib refresh $(date) ==="

  # 1. Pull latest upstreams. `lake update PhysLean` advances the lake
  # manifest's pinned commits for PhysLean (and transitively Mathlib).
  cd "$PROJECT_DIR/physlean-extract"
  lake update PhysLean

  # 2. Rebuild the dependency closure (this is the multi-hour leg).
  lake build PhysLean

  # 3. Re-extract the full corpus. The universal Lean→Expr translator
  # emits a structured AST for every theorem; the GA picks up new
  # building blocks automatically.
  cd "$PROJECT_DIR"
  just extract-mathlib

  # 4. Generate Lean axiom files for the prover (PhysLean catalog only;
  # the Mathlib corpus is consumed in-memory by the GA, not codegen-ed).
  just generate-axioms || echo "(generate-axioms failed; continuing)"
  (cd prover && lake build) || echo "(prover build failed; continuing)"

  # 5. Hot-reload the live API. Bypasses the systemctl restart that the
  # old recipe used, so existing GA workers don't lose their /api/seed
  # connections.
  if [[ -n "${ADMIN_TOKEN:-}" ]]; then
    echo "=== Hot-reloading API at $API_URL ==="
    curl -fsS -X POST \
      -H "Authorization: Bearer $ADMIN_TOKEN" \
      "$API_URL/api/admin/reload_corpus" | tee /dev/stderr || true
  else
    echo "ADMIN_TOKEN unset — skipping hot-reload. Restart the API to pick up the new corpus."
  fi

  echo "=== Done $(date) ==="
} 2>&1 | tee "$LOG"
