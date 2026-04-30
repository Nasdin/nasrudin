#!/usr/bin/env bash
# One-line installer for the Nasrudin discovery worker.
#
#   curl -fsSL https://nasrudin.org/install.sh | NASRUDIN_WORKER_KEY=nsk_worker_… bash
#
# What it does:
#   1. detects your OS and arch
#   2. installs `elan` (the Lean toolchain manager) if `lake` isn't on PATH
#   3. downloads the matching `nasrudin-worker-<os>-<arch>` bundle from
#      github.com/Nasdin/nasrudin/releases/latest
#   4. extracts to ~/.nasrudin/worker (override with NASRUDIN_WORKER_DIR)
#   5. starts ./run.sh, which warms the Mathlib cache on first run and
#      then submits verified theorems to api.nasrudin.org
#
# Required env: NASRUDIN_WORKER_KEY (nsk_worker_… from /api-keys)
# Optional env: NASRUDIN_API_URL    (default https://api.nasrudin.org)
#               NASRUDIN_WORKER_DIR (default $HOME/.nasrudin/worker)
#               NASRUDIN_WORKER_ID  (default $(hostname))

set -euo pipefail

REPO="Nasdin/nasrudin"
INSTALL_DIR="${NASRUDIN_WORKER_DIR:-$HOME/.nasrudin/worker}"

# ── 0. require key ─────────────────────────────────────────────────────────
if [ -z "${NASRUDIN_WORKER_KEY:-}" ]; then
  cat >&2 <<'EOF'
[install] error: NASRUDIN_WORKER_KEY is required.

  Get a worker key:
    1. Sign in at https://nasrudin.org/signin
    2. Open /api-keys → "+ New key" → Kind: Worker
    3. Copy the nsk_worker_… value

  Then run, replacing nsk_worker_… with the value you copied:
    curl -fsSL https://nasrudin.org/install.sh | NASRUDIN_WORKER_KEY=nsk_worker_… bash
EOF
  exit 1
fi

# ── 1. detect platform ─────────────────────────────────────────────────────
OS="$(uname -s | tr '[:upper:]' '[:lower:]')"
ARCH="$(uname -m)"
# Normalise common aliases.
case "$ARCH" in
  arm64)  ARCH="arm64"   ;;  # macOS reports arm64 directly
  aarch64) ARCH="aarch64" ;;
  x86_64|amd64) ARCH="x86_64" ;;
esac
case "$OS-$ARCH" in
  darwin-arm64)   SKU="darwin-arm64"   ;;
  darwin-x86_64)  SKU="darwin-x86_64"  ;;
  linux-x86_64)   SKU="linux-x86_64"   ;;
  linux-aarch64)  SKU="linux-aarch64"  ;;
  *)
    echo "[install] error: unsupported platform $OS-$ARCH" >&2
    echo "[install]   supported: darwin-arm64, darwin-x86_64, linux-x86_64, linux-aarch64" >&2
    exit 1
    ;;
esac
EXT="tar.gz"
echo "[install] platform: ${SKU}"

# ── 2. ensure elan + lake ──────────────────────────────────────────────────
if ! command -v lake >/dev/null 2>&1; then
  echo "[install] Lean toolchain (lake) not on PATH — installing elan…"
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  # elan-init writes to ~/.profile; pull it into THIS shell now.
  if [ -f "$HOME/.elan/env" ]; then
    # shellcheck disable=SC1091
    . "$HOME/.elan/env"
  else
    export PATH="$HOME/.elan/bin:$PATH"
  fi
  if ! command -v lake >/dev/null 2>&1; then
    echo "[install] error: elan installed but lake still not on PATH" >&2
    echo "[install]   restart your shell, then re-run this command" >&2
    exit 1
  fi
fi

# ── 3. download bundle ────────────────────────────────────────────────────
URL="https://github.com/${REPO}/releases/latest/download/nasrudin-worker-${SKU}.${EXT}"
TMPDIR="$(mktemp -d -t nasrudin-install.XXXXXX)"
trap 'rm -rf "$TMPDIR"' EXIT
TARBALL="$TMPDIR/bundle.${EXT}"
echo "[install] downloading $URL"
if ! curl --fail --location --silent --show-error --output "$TARBALL" "$URL"; then
  echo "[install] error: download failed (network? release missing?)" >&2
  exit 1
fi

# Optional sha256 verification — ignore if shasum unavailable or sidecar 404.
SHA_URL="${URL}.sha256"
if command -v shasum >/dev/null 2>&1; then
  SHA_FILE="$TMPDIR/bundle.sha256"
  if curl --fail --location --silent --show-error --output "$SHA_FILE" "$SHA_URL"; then
    EXPECTED="$(awk '{print $1}' "$SHA_FILE")"
    ACTUAL="$(shasum -a 256 "$TARBALL" | awk '{print $1}')"
    if [ "$EXPECTED" != "$ACTUAL" ]; then
      echo "[install] error: sha256 mismatch — expected $EXPECTED got $ACTUAL" >&2
      exit 1
    fi
    echo "[install] sha256 verified"
  fi
fi

# ── 4. extract ─────────────────────────────────────────────────────────────
mkdir -p "$INSTALL_DIR"
echo "[install] extracting to $INSTALL_DIR"
tar -xzf "$TARBALL" -C "$INSTALL_DIR" --strip-components=1
chmod +x "$INSTALL_DIR/nasrudin-worker" "$INSTALL_DIR/run.sh"

# ── 5. run ─────────────────────────────────────────────────────────────────
cd "$INSTALL_DIR"
echo
echo "[install] starting worker (Ctrl+C to stop)"
echo "[install]   bundle:   $INSTALL_DIR"
echo "[install]   api:      ${NASRUDIN_API_URL:-https://api.nasrudin.org}"
echo "[install]   worker_id: ${NASRUDIN_WORKER_ID:-$(hostname)}"
echo
exec ./run.sh
