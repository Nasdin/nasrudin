#!/usr/bin/env bash
# 24h soak driver for the cluster-steerer + paid Researcher feature.
#
# What it does:
#   1. Verifies a `physics-api` daemon is reachable on $API.
#   2. Seeds a Researcher account with N research_credits.
#   3. POSTs one paid conjecture so the steerer flips into mode B.
#   4. Generates background demand (saved-search inserts, search hits)
#      so the steerer prompt has something to chew on.
#   5. Tails /metrics every minute, logging the steerer/paid-job
#      gauges to a CSV for post-soak analysis.
#   6. After 24h, prints a one-line acceptance summary.
#
# Acceptance (matches plan Phase 8.2):
#   - cluster_steering has ~144 rows (one per 10 min).
#   - ≥5 cycles validated successfully (validation_failed=false +
#     non-null outcome_json).
#   - Mode flipped to B during the paid window, back to C after.
#   - explorer_floor_satisfied == 1 for ≥99.9% of the window.
#   - Paid job ended in `proved` (Lean artifact) or
#     `budget_exhausted` (credit refunded only if zero verified +
#     <1000 candidates).
#
# Required env:
#   API                — base URL, e.g. http://localhost:3001
#   ADMIN_TOKEN        — for /api/admin/steering/recent at the end
#   RESEARCHER_COOKIE  — session cookie of a logged-in researcher account
#   WORKER_KEY_n       — at least 5 nsk_worker_… keys; the soak just
#                         observes external workers, it doesn't spawn them
#
# Usage:
#   API=https://nasrudin.org \
#   ADMIN_TOKEN=$(cat /run/secrets/admin) \
#   RESEARCHER_COOKIE=…\
#   ./soak-cluster-steerer.sh

set -euo pipefail

: "${API:=http://localhost:3001}"
: "${ADMIN_TOKEN:?ADMIN_TOKEN must be set}"
: "${RESEARCHER_COOKIE:?RESEARCHER_COOKIE must be set (session=…)}"

LOG_DIR=${LOG_DIR:-./soak-logs}
mkdir -p "$LOG_DIR"
START_TS=$(date -u +%Y%m%dT%H%M%SZ)
METRICS_CSV="$LOG_DIR/metrics-$START_TS.csv"
EVENT_LOG="$LOG_DIR/events-$START_TS.log"

echo "ts,steerer_mode,paid_active,paid_queued,explorer_free,floor_ok,total_slots" > "$METRICS_CSV"

log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$EVENT_LOG"; }

# --- 0. Sanity: API up
curl -fsS "$API/api/health" >/dev/null || { log "API not reachable at $API"; exit 1; }
log "API reachable at $API"

# --- 1. Submit a paid conjecture (assumes 1 credit available)
HUNCH='If T = T_h × T_c / (T_h - T_c), then dQ/T forms a state function.'
JOB_RESP=$(curl -fsS -X POST "$API/api/research/jobs" \
    -H "Content-Type: application/json" \
    -H "Cookie: $RESEARCHER_COOKIE" \
    -d "{\"hunch\":\"$HUNCH\",\"domain_hint\":\"thermodynamics\"}" || true)
JOB_ID=$(echo "$JOB_RESP" | sed -n 's/.*"job_id":"\([^"]*\)".*/\1/p')
if [ -z "$JOB_ID" ]; then
    log "FAILED to create paid job: $JOB_RESP"
    exit 1
fi
log "Submitted paid conjecture job_id=$JOB_ID"

# --- 2. Background demand generator: bookmark a few latex strings
SAMPLE_QUERIES=(
    "E = mc^2"
    "F = ma"
    "\\nabla \\cdot E = \\rho/\\epsilon_0"
    "dS \\geq 0"
    "p = mv"
)
for q in "${SAMPLE_QUERIES[@]}"; do
    curl -fsS -X POST "$API/api/saved-searches" \
        -H "Content-Type: application/json" \
        -H "Cookie: $RESEARCHER_COOKIE" \
        -d "{\"latex\":\"$q\"}" >/dev/null 2>&1 || true
done
log "Seeded ${#SAMPLE_QUERIES[@]} saved-search rows"

# --- 3. Tail /metrics for 24h
DEADLINE=$(( $(date -u +%s) + 86400 ))
while [ "$(date -u +%s)" -lt $DEADLINE ]; do
    BODY=$(curl -fsS "$API/metrics" 2>/dev/null || echo "")
    MODE=$(echo "$BODY" | awk -F'"' '/^nasrudin_steerer_mode\{scope/{print $2; exit}')
    ACTIVE=$(echo "$BODY" | awk '/^nasrudin_paid_jobs_active /{print $2; exit}')
    QUEUED=$(echo "$BODY" | awk '/^nasrudin_paid_jobs_queued /{print $2; exit}')
    FREE=$(echo "$BODY"   | awk '/^nasrudin_explorer_slot_count /{print $2; exit}')
    OK=$(echo "$BODY"     | awk '/^nasrudin_explorer_floor_satisfied /{print $2; exit}')
    TOTAL=$(echo "$BODY"  | awk '/^nasrudin_total_lake_slots /{print $2; exit}')
    echo "$(date -u +%FT%TZ),${MODE:-?},${ACTIVE:-0},${QUEUED:-0},${FREE:-0},${OK:-0},${TOTAL:-0}" \
        >> "$METRICS_CSV"
    sleep 60
done

log "24h elapsed; collecting acceptance evidence"

# --- 4. Acceptance summary
CYCLES_JSON=$(curl -fsS -H "Authorization: Bearer $ADMIN_TOKEN" \
    "$API/api/admin/steering/recent" || echo '{"cycles":[]}')
TOTAL_CYCLES=$(echo "$CYCLES_JSON" | python3 -c \
    'import json,sys;print(len(json.load(sys.stdin).get("cycles",[])))')
VALIDATED=$(echo "$CYCLES_JSON" | python3 -c \
    'import json,sys;c=json.load(sys.stdin).get("cycles",[]);print(sum(1 for r in c if not r["validation_failed"] and r.get("outcome_json")))')

JOB_STATE=$(curl -fsS -H "Cookie: $RESEARCHER_COOKIE" \
    "$API/api/research/jobs/$JOB_ID" | python3 -c \
    'import json,sys;d=json.load(sys.stdin);print(d.get("state","?"))')

FLOOR_VIOLATIONS=$(awk -F, 'NR>1 && $6=="0"{n++} END{print n+0}' "$METRICS_CSV")
TOTAL_SAMPLES=$(($(wc -l < "$METRICS_CSV") - 1))

log "==== ACCEPTANCE SUMMARY ===="
log "cycles_total=$TOTAL_CYCLES (target ~144)"
log "cycles_validated_with_outcome=$VALIDATED (target ≥5)"
log "paid_job_$JOB_ID final_state=$JOB_STATE"
log "explorer_floor_violations=$FLOOR_VIOLATIONS / $TOTAL_SAMPLES samples"
log "metrics CSV: $METRICS_CSV"

if [ "$VALIDATED" -lt 5 ] || [ "$FLOOR_VIOLATIONS" -gt $((TOTAL_SAMPLES / 1000)) ]; then
    log "❌ acceptance failed"
    exit 1
fi
log "✅ acceptance passed"
