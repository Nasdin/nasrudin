#!/usr/bin/env bash
# Nasrudin discovery worker — public bundle launcher.
#
# Required env: NASRUDIN_WORKER_KEY (nsk_worker_…)
# Optional env: NASRUDIN_API_URL (default https://api.nasrudin.org)
#               NASRUDIN_WORKER_ID (default $(hostname))

set -euo pipefail

cd "$(dirname "$(realpath "$0")")"

if [ -z "${NASRUDIN_WORKER_KEY:-}" ]; then
  echo "error: NASRUDIN_WORKER_KEY is required" >&2
  echo "  Get one at https://nasrudin.org/api-keys (Kind: Worker)" >&2
  exit 1
fi

export NASRUDIN_API_URL="${NASRUDIN_API_URL:-https://api.nasrudin.org}"
export NASRUDIN_WORKER_ID="${NASRUDIN_WORKER_ID:-$(hostname)}"

if ! command -v lake >/dev/null 2>&1; then
  echo "error: 'lake' (Lean toolchain) not found on \$PATH" >&2
  echo "  Install with:" >&2
  echo "    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y" >&2
  echo "  Then re-source ~/.profile or restart your shell." >&2
  exit 1
fi

if [ ! -d prover/.lake ]; then
  echo "[worker] first run: warming Mathlib cache (this takes a few minutes)..."
  (cd prover && lake exe cache get >/dev/null 2>&1 || true)
fi

echo "[worker] api=$NASRUDIN_API_URL  id=$NASRUDIN_WORKER_ID"
exec ./nasrudin-worker --verify ./prover "$@"
