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

# ── Corpus freshness policy ──────────────────────────────────────────────
# physics-api at boot reads catalog.json + math_corpus.json. We bake them
# into the release tarball so the droplet doesn't need a Lean toolchain
# at provision time. Mathlib + PhysLean evolve independently of this
# repo, so a stale corpus on disk produces a deploy that's behind
# upstream by however long since the last `just extract-mathlib` run.
#
# Defaults:
#   STALE_AFTER_DAYS=14    refuse to ship if the corpus is older than this
#   AUTO_REFRESH=1         when stale, auto-run `just refresh-corpus` to
#                          pull latest upstreams + re-extract
#
# Override at the call site:
#   AUTO_REFRESH=0 deploy/scripts/build-release.sh   # fail loudly instead
#   STALE_AFTER_DAYS=1 deploy/scripts/build-release.sh # daily refresh
STALE_AFTER_DAYS="${STALE_AFTER_DAYS:-14}"
AUTO_REFRESH="${AUTO_REFRESH:-1}"

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
mkdir -p "$OUT_DIR"/bin "$OUT_DIR/frontend" "$OUT_DIR/prover" "$OUT_DIR/lib" \
         "$OUT_DIR/deploy/systemd" "$OUT_DIR/deploy/scripts"
mkdir -p "$BUILD_CACHE/target" "$BUILD_CACHE/registry"

# ── 1. Cross-compile Rust binaries via docker (linux/amd64) ──────────────
echo "[build] cross-compiling rust binaries via docker (linux/amd64)..."
echo "        (slow on apple silicon — qemu emulation. cache mounted at $BUILD_CACHE)"
# Apple Silicon under qemu can OOM-kill the Linux VM if cargo spawns too
# many parallel rustc workers — large monomorphisations (e.g. axum,
# fastembed, sea-orm) easily push a single compile-job past 2 GiB. We cap
# CARGO_BUILD_JOBS based on the host memory and Docker memory allocation.
# 2 jobs is conservative and finishes the cold build in ~20 min on a
# 16 GiB MacBook Pro; bump via CARGO_BUILD_JOBS_OVERRIDE when you have
# headroom or are running on a more capable host.
CARGO_BUILD_JOBS_DEFAULT=2
CARGO_BUILD_JOBS_BUILD="${CARGO_BUILD_JOBS_OVERRIDE:-$CARGO_BUILD_JOBS_DEFAULT}"
echo "[build] using CARGO_BUILD_JOBS=$CARGO_BUILD_JOBS_BUILD inside docker"
# Memory limit on the container itself: Docker Desktop on Apple Silicon
# defaults to ~8 GiB but the VM can be sized higher. Setting --memory
# tells the qemu emulator to throttle at the limit instead of swap-thrashing
# the host. 6g leaves headroom for Docker's own overhead and keeps the
# host responsive while builds run.
#
# Image: rust:1.95-trixie (Debian 13, glibc 2.39). Two reasons:
#   * matches the Ubuntu 24.04 droplet's glibc 2.39 ABI
#   * trixie has libonnxruntime-dev in apt, which we use to dynamic-link
#     ort-sys instead of fighting pyke's prebuilt blob (the prebuilt
#     intermittently fails to extract under cargo, and even when it works
#     it requires glibc ≥ 2.38 — which rules out bookworm). Trixie also
#     ships gcc 14, which compiles librocksdb-sys cleanly.
docker run --rm --platform linux/amd64 \
  --memory=6g \
  --memory-swap=10g \
  -v "$PWD/engine":/src \
  -v "$PWD/$BUILD_CACHE/target":/cargo-target \
  -v "$PWD/$BUILD_CACHE/registry":/cargo-home \
  -v "$PWD/$OUT_DIR/lib":/release-lib \
  -e CARGO_TARGET_DIR=/cargo-target \
  -e CARGO_HOME=/cargo-home \
  -e CARGO_BUILD_JOBS="$CARGO_BUILD_JOBS_BUILD" \
  `# ORT_LIB_LOCATION + ORT_PREFER_DYNAMIC_LINK=1 take ort-sys's "system` \
  `# library" code path (build/main.rs around line 45): emit -lonnxruntime` \
  `# (dynamic) and -L /usr/lib/x86_64-linux-gnu, instead of falling through` \
  `# to the prebuilt-blob download (which is broken under cargo for v2.0.0-rc.12).` \
  `# Without LIB_LOCATION set, ort-sys falls into the download path even with` \
  `# PREFER_DYNAMIC_LINK on. With both set + libonnxruntime-dev installed via` \
  `# apt below, ort-sys links cleanly. We bundle the .so into the release tarball.` \
  -e ORT_LIB_LOCATION=/usr/lib/x86_64-linux-gnu \
  -e ORT_PREFER_DYNAMIC_LINK=1 \
  -w /src \
  rust:1.95-trixie \
  bash -c "set -e
    apt-get update -qq
    # libonnxruntime-dev provides /usr/lib/x86_64-linux-gnu/libonnxruntime.so
    # + headers; with ORT_PREFER_DYNAMIC_LINK=1 above, ort-sys's build
    # script links our binaries against this .so instead of attempting
    # to download + extract pyke's prebuilt static blob.
    apt-get install -y --no-install-recommends pkg-config libssl-dev clang cmake libonnxruntime-dev >/dev/null
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
      --bin nasrudin-elaborator \
      --bin backfill_existing_lean
    # Stage the .so + version chain into the release tarball, plus
    # everything libonnxruntime transitively needs that Ubuntu 24.04
    # noble doesn't ship (no libonnxruntime in noble apt). We grab the
    # full Trixie set so the droplet has a self-contained ONNX runtime.
    # ldd /usr/lib/x86_64-linux-gnu/libonnxruntime.so.1.21 lists:
    # libXNNPACK, libpthreadpool, libonnx, libonnx_proto, libprotobuf.32,
    # libcpuinfo, libre2, libabsl_*. We bundle all of those (libstdc++/m/c
    # are system-level on the droplet, no need). provision-native.sh installs
    # them at /opt/nasrudin/lib/; systemd unit pins LD_LIBRARY_PATH.
    cd /usr/lib/x86_64-linux-gnu/
    cp -aP libonnxruntime.so* libonnx.so* libonnx_proto.so* libXNNPACK.so* \
           libpthreadpool.so* libprotobuf.so* libcpuinfo.so* libre2.so* \
           libabsl_*.so* /release-lib/ 2>&1 | head -3 || true
    cp -aP /lib/x86_64-linux-gnu/libabsl_*.so* /release-lib/ 2>/dev/null || true
    echo '[build] bundled '\$(ls /release-lib/ | wc -l)' onnxruntime + transitive deps'
  "

for bin in physics-api migrate worker nasrudin-elaborator backfill_existing_lean; do
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
#
# Hard-require VITE_FIREBASE_* up front. Vite silently bakes empty
# strings if these aren't exported in the environment, and the prod
# bundle crashes at runtime ("Missing env var: VITE_FIREBASE_API_KEY").
# Better to fail the build with a clear pointer than ship a dead
# /signin page. Source these from the project root .env via:
#   set -a && . ./.env && set +a && deploy/scripts/deploy.sh nasrudin-prod
for var in VITE_FIREBASE_API_KEY VITE_FIREBASE_AUTH_DOMAIN \
           VITE_FIREBASE_PROJECT_ID VITE_FIREBASE_STORAGE_BUCKET \
           VITE_FIREBASE_MESSAGING_SENDER_ID VITE_FIREBASE_APP_ID; do
  if [ -z "${!var:-}" ]; then
    echo "[build] error: $var is not set in the environment." >&2
    echo "        Source it (and the rest of the VITE_FIREBASE_* block)" >&2
    echo "        from .env before invoking deploy:" >&2
    echo "        set -a && . ./.env && set +a && deploy/scripts/deploy.sh ..." >&2
    exit 1
  fi
done

echo "[build] building frontend (pnpm install + build)..."
pnpm install --frozen-lockfile --silent
(cd nasrudin-frontend && \
  VITE_API_URL="https://api.nasrudin.org" \
  VITE_STRIPE_SPONSOR_PAYMENT_LINK="${VITE_STRIPE_SPONSOR_PAYMENT_LINK:-https://donate.stripe.com/aFaaEXg2KgjZeCibEHbsc00}" \
  VITE_FIREBASE_API_KEY="${VITE_FIREBASE_API_KEY:-}" \
  VITE_FIREBASE_AUTH_DOMAIN="${VITE_FIREBASE_AUTH_DOMAIN:-}" \
  VITE_FIREBASE_PROJECT_ID="${VITE_FIREBASE_PROJECT_ID:-}" \
  VITE_FIREBASE_STORAGE_BUCKET="${VITE_FIREBASE_STORAGE_BUCKET:-}" \
  VITE_FIREBASE_MESSAGING_SENDER_ID="${VITE_FIREBASE_MESSAGING_SENDER_ID:-}" \
  VITE_FIREBASE_APP_ID="${VITE_FIREBASE_APP_ID:-}" \
  pnpm build)

# `pnpm deploy --prod` produces an isolated directory (package.json +
# prod-only node_modules), no symlinks. We then drop the built dist/ on
# top so node can resolve `react` etc. from ./node_modules at runtime.
echo "[build] producing prod-only node_modules via pnpm deploy..."
rm -rf "$OUT_DIR/frontend"
# --node-linker=hoisted: flat node_modules tree (no symlinks) so node's ESM
# resolver can walk react -> exports['./jsx-runtime'] correctly. The default
# isolated/symlink layout breaks ESM resolution under realpath-following.
# --frozen-lockfile: without it `pnpm deploy` RE-RESOLVES dependencies from
# the package.json caret ranges, ignoring pnpm-lock.yaml ("prohibits to read
# or write a lockfile" warning). That drifted @tanstack/react-router from the
# pinned 1.169.1 up to 1.170.8 — a minor bump that ships a breaking hydration
# change and produced a global client-side "Invariant failed" → blank site.
# Forcing the frozen lockfile keeps the deployed tree identical to the tested
# `pnpm install --frozen-lockfile` above.
pnpm --filter nasrudin-frontend deploy --prod --frozen-lockfile --node-linker=hoisted "$OUT_DIR/frontend"
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

# ── 3.5. PhysLean catalog + math_corpus (with freshness gate) ────────────
# physics-api at boot loads:
#   <PROVER_ROOT>/../physlean-extract/output/catalog.json     (PhysLean axioms)
#   <PROVER_ROOT>/../physlean-extract/output/math_corpus.json (Mathlib substrate)
# Boot panics if math_corpus is missing or has <10 000 entries.
# We bake them into the tarball so the droplet doesn't need a Lean toolchain
# for cold start. The droplet's PROVER_ROOT is /opt/nasrudin/prover, so the
# corpus lands at /opt/nasrudin/physlean-extract/output/.

stale_after_seconds=$((STALE_AFTER_DAYS * 86400))
needs_refresh=0

if [ ! -f physlean-extract/output/catalog.json ] || \
   [ ! -f physlean-extract/output/math_corpus.json ]; then
  echo "[build] catalog or math_corpus missing — refresh required."
  needs_refresh=1
else
  # Use the older of the two timestamps. `stat -f%m` (BSD/macOS),
  # `stat -c%Y` (Linux). build-release.sh runs on the host, not in
  # docker, so it sees host stat.
  cat_mtime=$(stat -f%m physlean-extract/output/catalog.json 2>/dev/null \
              || stat -c%Y physlean-extract/output/catalog.json)
  cor_mtime=$(stat -f%m physlean-extract/output/math_corpus.json 2>/dev/null \
              || stat -c%Y physlean-extract/output/math_corpus.json)
  oldest=$(( cat_mtime < cor_mtime ? cat_mtime : cor_mtime ))
  age=$(( $(date +%s) - oldest ))
  age_days=$(( age / 86400 ))
  echo "[build] corpus age: ${age_days} day(s) (limit: ${STALE_AFTER_DAYS})"
  if [ "$age" -gt "$stale_after_seconds" ]; then
    echo "[build] corpus exceeds STALE_AFTER_DAYS=${STALE_AFTER_DAYS} — refresh required."
    needs_refresh=1
  fi

  # Size sanity check — a +all extraction yields ~290 MB, narrow ~14 MB.
  # Anything under 5 MB suggests a truncated / failed extraction.
  corpus_size=$(stat -f%z physlean-extract/output/math_corpus.json 2>/dev/null \
                || stat -c%s physlean-extract/output/math_corpus.json)
  if [ "$corpus_size" -lt 5000000 ]; then
    echo "[build] math_corpus.json is only $corpus_size bytes — looks truncated."
    needs_refresh=1
  fi
fi

if [ "$needs_refresh" -eq 1 ]; then
  if [ "$AUTO_REFRESH" -eq 1 ]; then
    if ! command -v just >/dev/null 2>&1; then
      echo "[build] error: just is not on PATH — install via 'cargo install just' or set AUTO_REFRESH=0 to opt out" >&2
      exit 1
    fi
    if ! command -v lake >/dev/null 2>&1; then
      echo "[build] error: lake is not on PATH — install via 'curl https://elan.lean-lang.org/elan-init.sh -sSf | sh' or set AUTO_REFRESH=0" >&2
      exit 1
    fi
    echo "[build] auto-refreshing corpus from upstream (this takes ~5–10 min)..."
    just refresh-corpus
  else
    echo "[build] error: corpus is stale or missing and AUTO_REFRESH=0 — run 'just refresh-corpus' first or unset AUTO_REFRESH=0" >&2
    exit 1
  fi
fi

echo "[build] copying PhysLean catalog + Mathlib math_corpus..."
mkdir -p "$OUT_DIR/physlean-extract/output"
cp physlean-extract/output/catalog.json "$OUT_DIR/physlean-extract/output/"
cp physlean-extract/output/math_corpus.json "$OUT_DIR/physlean-extract/output/"
echo "[build] catalog + corpus: $(du -sh "$OUT_DIR/physlean-extract/output/" | cut -f1)"

# ── 4. Deploy assets ──────────────────────────────────────────────────────
cp deploy/Caddyfile.native "$OUT_DIR/deploy/Caddyfile"
cp deploy/systemd/nasrudin-api.service "$OUT_DIR/deploy/systemd/"
cp deploy/systemd/nasrudin-frontend.service "$OUT_DIR/deploy/systemd/"
cp deploy/systemd/nasrudin-worker.service "$OUT_DIR/deploy/systemd/"
cp deploy/systemd/nasrudin-elaborator.service "$OUT_DIR/deploy/systemd/"
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
