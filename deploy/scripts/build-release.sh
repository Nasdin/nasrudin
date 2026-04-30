#!/usr/bin/env bash
# Build a deployable artifact for the nasrudin-prod droplet (linux/amd64).
#
# Output:
#   dist/release.tar.gz containing:
#     bin/                  cross-compiled Rust binaries
#                             (physics-api, migrate, worker, backfill_existing_lean)
#     frontend/             pre-built TanStack Start SSR bundle (dist/{client,server})
#     prover/               PhysicsGenerator source + lakefile (no .lake cache —
#                             droplet runs `lake exe cache get` at provision time)
#     deploy/Caddyfile      reverse-proxy config (native; localhost ports)
#     deploy/systemd/*      systemd unit files
#     deploy/scripts/provision-native.sh
#     .env.example
#
# Requires: docker daemon running (for linux/amd64 cross-compile), pnpm.
# Apple Silicon hosts: cargo build runs under qemu — expect 15–30 min on
# first build (no cache); ~2–5 min subsequent (incremental).

set -euo pipefail
cd "$(dirname "$0")/../.."

OUT_DIR=dist/release
TARBALL=dist/release.tar.gz
BUILD_CACHE=dist/build-cache

if ! docker info >/dev/null 2>&1; then
  echo "[build] error: docker daemon not running" >&2
  exit 1
fi
if ! command -v pnpm >/dev/null 2>&1; then
  echo "[build] error: pnpm not on PATH" >&2
  exit 1
fi

echo "[build] cleaning $OUT_DIR / $TARBALL"
rm -rf "$OUT_DIR" "$TARBALL"
mkdir -p "$OUT_DIR"/bin "$OUT_DIR/frontend" "$OUT_DIR/prover" \
         "$OUT_DIR/deploy/systemd" "$OUT_DIR/deploy/scripts"
mkdir -p "$BUILD_CACHE/target" "$BUILD_CACHE/registry"

# ── 1. Cross-compile Rust binaries via docker (linux/amd64) ──────────────
echo "[build] cross-compiling rust binaries via docker (linux/amd64)..."
echo "        (slow on apple silicon — qemu emulation. cache mounted at $BUILD_CACHE)"
docker run --rm --platform linux/amd64 \
  -v "$PWD/engine":/src \
  -v "$PWD/$BUILD_CACHE/target":/cargo-target \
  -v "$PWD/$BUILD_CACHE/registry":/cargo-home \
  -e CARGO_TARGET_DIR=/cargo-target \
  -e CARGO_HOME=/cargo-home \
  -w /src \
  rust:1.95-bookworm \
  bash -c "set -e
    apt-get update -qq
    apt-get install -y --no-install-recommends pkg-config libssl-dev clang cmake >/dev/null
    # Drop fingerprints for our local crates so any stale incremental state
    # from a prior killed build (e.g. mid-pg compile) can't poison the run.
    # Workspace deps from /usr/local/cargo/registry are kept — that's the slow part.
    cargo clean --release -p nasrudin-pg -p nasrudin-api -p nasrudin-ga \
                          -p nasrudin-derive -p nasrudin-core \
                          -p nasrudin-rocks -p nasrudin-lean-bridge \
                          -p nasrudin-embed -p nasrudin-llm 2>/dev/null || true
    cargo build --release --locked \
      --bin physics-api \
      --bin migrate \
      --bin worker \
      --bin backfill_existing_lean
  "

for bin in physics-api migrate worker backfill_existing_lean; do
  src="$BUILD_CACHE/target/release/$bin"
  if [ ! -f "$src" ]; then
    echo "[build] error: expected $src not produced" >&2
    exit 1
  fi
  cp "$src" "$OUT_DIR/bin/$bin"
  chmod +x "$OUT_DIR/bin/$bin"
done
echo "[build] binaries:"
ls -lh "$OUT_DIR/bin/"

# ── 2. Build frontend SSR bundle ──────────────────────────────────────────
# VITE_* vars are baked into the client bundle at build time, so they have
# to be set HERE — runtime systemd env doesn't reach the client code.
echo "[build] building frontend (pnpm install + build)..."
pnpm install --frozen-lockfile --silent
(cd nasrudin-frontend && \
  VITE_API_URL="${VITE_API_URL:-https://api.nasrudin.org}" \
  VITE_STRIPE_SPONSOR_PAYMENT_LINK="${VITE_STRIPE_SPONSOR_PAYMENT_LINK:-https://donate.stripe.com/aFaaEXg2KgjZeCibEHbsc00}" \
  pnpm build)

# `pnpm deploy --prod` produces an isolated directory (package.json +
# prod-only node_modules), no symlinks. We then drop the built dist/ on
# top so node can resolve `react` etc. from ./node_modules at runtime.
echo "[build] producing prod-only node_modules via pnpm deploy..."
rm -rf "$OUT_DIR/frontend"
# --node-linker=hoisted: flat node_modules tree (no symlinks) so node's ESM
# resolver can walk react -> exports['./jsx-runtime'] correctly. The default
# isolated/symlink layout breaks ESM resolution under realpath-following.
pnpm --filter nasrudin-frontend deploy --prod --node-linker=hoisted "$OUT_DIR/frontend"
cp -R nasrudin-frontend/dist/. "$OUT_DIR/frontend/"
# TanStack Start v1's node-server preset emits a Web-Fetch handler module,
# not a standalone server. This wrapper boots a Node http listener.
cp deploy/frontend-server.mjs "$OUT_DIR/frontend/server/server.mjs"
if [ ! -f nasrudin-frontend/dist/server/ssr.js ] && [ ! -f nasrudin-frontend/dist/server/index.mjs ]; then
  echo "[build] warning: expected server entry not found in nasrudin-frontend/dist/server/" >&2
fi
echo "[build] frontend bundle (incl. prod node_modules): $(du -sh "$OUT_DIR/frontend/" | cut -f1)"

# ── 3. Prover source (no .lake; droplet runs `lake exe cache get`) ────────
echo "[build] copying prover source..."
cp -R prover/PhysicsGenerator "$OUT_DIR/prover/"
cp prover/PhysicsGenerator.lean prover/lakefile.lean prover/lake-manifest.json prover/lean-toolchain "$OUT_DIR/prover/"
[ -d prover/scripts ] && cp -R prover/scripts "$OUT_DIR/prover/" || true

# ── 4. Deploy assets ──────────────────────────────────────────────────────
cp deploy/Caddyfile.native "$OUT_DIR/deploy/Caddyfile"
cp deploy/systemd/nasrudin-api.service "$OUT_DIR/deploy/systemd/"
cp deploy/systemd/nasrudin-frontend.service "$OUT_DIR/deploy/systemd/"
cp deploy/systemd/nasrudin-worker.service "$OUT_DIR/deploy/systemd/"
cp deploy/scripts/issue_worker_key.py "$OUT_DIR/deploy/scripts/"
chmod +x "$OUT_DIR/deploy/scripts/issue_worker_key.py"
cp deploy/scripts/provision-native.sh "$OUT_DIR/deploy/scripts/"
chmod +x "$OUT_DIR/deploy/scripts/provision-native.sh"
cp .env.example "$OUT_DIR/.env.example"

# ── 5. Tarball ────────────────────────────────────────────────────────────
# COPYFILE_DISABLE=1 keeps BSD tar (default on macOS) from emitting
# AppleDouble (._*) sidecar files for files with extended attributes.
echo "[build] tarballing..."
(cd dist && COPYFILE_DISABLE=1 tar czf release.tar.gz release/)
echo "[build] done: $TARBALL ($(du -h "$TARBALL" | cut -f1))"
