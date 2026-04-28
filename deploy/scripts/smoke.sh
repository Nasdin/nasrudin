#!/usr/bin/env bash
# Phase 9 post-deploy smoke test. Run from a developer machine against either
# https://nasrudin.org (live) or http://localhost (local docker compose).
#
# Required env:
#   NASRUDIN_API_PUBLIC_URL       — e.g. https://api.nasrudin.org or http://localhost:3001
#   NASRUDIN_FRONTEND_PUBLIC_URL  — e.g. https://nasrudin.org or http://localhost:3000
#   NASRUDIN_INTERNAL_WORKER_KEY  — for the ingest assertions
#
# Exit non-zero on any failed assertion.

set -uo pipefail

API="${NASRUDIN_API_PUBLIC_URL:-http://localhost:3001}"
FRONTEND="${NASRUDIN_FRONTEND_PUBLIC_URL:-http://localhost:3000}"
KEY="${NASRUDIN_INTERNAL_WORKER_KEY:-}"

PASS=0
FAIL=0
FAIL_NAMES=()

assert() {
  local name=$1; shift
  if "$@"; then
    echo "✓ $name"
    PASS=$((PASS + 1))
  else
    echo "✗ $name"
    FAIL=$((FAIL + 1))
    FAIL_NAMES+=("$name")
  fi
}

# --- Frontend renders ----------------------------------------------------------
assert "frontend / renders" \
  bash -c "curl -fsS '$FRONTEND/' | grep -qi nasrudin"

# --- API health is well-formed ------------------------------------------------
assert "api /api/health → ok" \
  bash -c "curl -fsS '$API/api/health' | jq -e '.db == \"ok\" and .rocks == \"ok\" and (.queue_depth | type == \"number\")' >/dev/null"

# --- Read endpoints -----------------------------------------------------------
assert "GET /api/theorems?limit=1" \
  bash -c "curl -fsS '$API/api/theorems?limit=1' | jq -e 'has(\"theorems\") and has(\"total\")' >/dev/null"

assert "GET /api/domains" \
  bash -c "curl -fsS '$API/api/domains' >/dev/null"

assert "GET /api/axioms" \
  bash -c "curl -fsS '$API/api/axioms' >/dev/null"

assert "GET /api/workers" \
  bash -c "curl -fsS '$API/api/workers' | jq -e 'type == \"array\"' >/dev/null"

# --- SSE streams (≥1 byte within 20s) -----------------------------------------
assert "SSE /api/events/discoveries open + ping" \
  bash -c "timeout 20 curl -fsSN '$API/api/events/discoveries' | head -c 32 | grep -qE 'ping|theorem_'"

assert "SSE /api/events/stats open + ping" \
  bash -c "timeout 20 curl -fsSN '$API/api/events/stats' | head -c 32 | grep -qE 'ping|ga_|worker_'"

# --- Ingest path (requires key) -----------------------------------------------
if [ -z "$KEY" ]; then
  echo "skip: ingest assertions (NASRUDIN_INTERNAL_WORKER_KEY not set)"
else
  TIMESTAMP="$(date +%s)"
  PAYLOAD_OK="$(cat <<EOF
{"worker_id":"in-proc-worker-1","engine_git_sha":"smoke","lean_version":"4.27.0",
 "theorems":[{"canonical_statement":"Smoke_${TIMESTAMP}","domain":"PureMath",
              "lean_source":"theorem t : True := trivial","chain":[],"axioms_used":[]}]}
EOF
)"
  assert "POST /api/ingest accepts a clean theorem" \
    bash -c "curl -fsS -X POST '$API/api/ingest' \
      -H 'authorization: Bearer $KEY' -H 'content-type: application/json' \
      -d '$PAYLOAD_OK' | \
      jq -e '.results[0].status.kind | test(\"Pending|Duplicate\")' >/dev/null"

  PAYLOAD_AXIOM="$(cat <<EOF
{"worker_id":"in-proc-worker-1","engine_git_sha":"smoke","lean_version":"4.27.0",
 "theorems":[{"canonical_statement":"Evil_${TIMESTAMP}","domain":"PureMath",
              "lean_source":"axiom evil : True\ntheorem t : True := evil","chain":[],"axioms_used":[]}]}
EOF
)"
  assert "axiom firewall rejects fresh axiom in lean_source" \
    bash -c "curl -fsS -X POST '$API/api/ingest' \
      -H 'authorization: Bearer $KEY' -H 'content-type: application/json' \
      -d '$PAYLOAD_AXIOM' | \
      jq -e '.results[0].status.kind == \"Rejected\"' >/dev/null"
fi

echo
echo "Passed: $PASS  Failed: $FAIL"
if [ $FAIL -gt 0 ]; then
  echo "Failed assertions:"
  for n in "${FAIL_NAMES[@]}"; do echo "  - $n"; done
  exit 1
fi
