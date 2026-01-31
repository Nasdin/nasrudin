#!/usr/bin/env bash
# Weekly PhysLean refresh — add to crontab:
#   0 3 * * 0 /opt/physics-generator/deploy/cron-refresh.sh
set -euo pipefail
PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_DIR"
LOG="logs/refresh-$(date +%Y%m%d).log"
mkdir -p logs

{
  echo "=== PhysLean refresh $(date) ==="
  just extract-physlean
  just generate-axioms
  cd prover && lake build
  echo "=== Refresh complete. Restarting engine... ==="
  systemctl --user restart physics-generator || true
  echo "=== Done $(date) ==="
} 2>&1 | tee "$LOG"
