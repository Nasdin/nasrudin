#!/usr/bin/env bash
# Cross-compile the public discovery-worker binary for every supported
# host platform LOCALLY (no GitHub Actions). Output:
#
#   dist/worker-release/nasrudin-worker-linux-x86_64.tar.gz
#   dist/worker-release/nasrudin-worker-darwin-arm64.tar.gz
#   dist/worker-release/nasrudin-worker-darwin-x86_64.tar.gz
#   dist/worker-release/nasrudin-worker-windows-x86_64.zip
#   …each with a matching .sha256 sidecar.
#
# Each bundle contains: nasrudin-worker[.exe], run.sh / run.ps1,
# README.md, prover/ (source — droplet runs `lake exe cache get`).
#
# Prereqs (script will tell you if any are missing):
#   - docker (for linux cross-compile via qemu/--platform linux/amd64)
#   - rustup (auto-adds x86_64-apple-darwin, x86_64-pc-windows-gnu)
#   - mingw-w64 (for windows: `brew install mingw-w64`). Skipped if absent.
#
# Env knobs:
#   ENABLE_WIN=0     skip windows even if mingw is present
#   ENABLE_DARWIN_X86=0  skip Intel-mac build (default builds it)

set -euo pipefail
cd "$(dirname "$0")/../.."

OUT_DIR=dist/worker-release
BUILD_CACHE=dist/build-cache
ENABLE_WIN="${ENABLE_WIN:-1}"
ENABLE_DARWIN_X86="${ENABLE_DARWIN_X86:-1}"

if ! docker info >/dev/null 2>&1; then
  echo "[worker] error: docker daemon not running (needed for linux build)" >&2
  exit 1
fi

echo "[worker] cleaning $OUT_DIR"
rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR" "$BUILD_CACHE/linux-target" "$BUILD_CACHE/cargo-home"

# ── 1. linux x86_64 via docker (qemu on apple silicon) ───────────────────
echo "[worker] [1/4] linux x86_64 (docker)..."
docker run --rm --platform linux/amd64 \
  -v "$PWD/engine":/src \
  -v "$PWD/$BUILD_CACHE/linux-target":/cargo-target \
  -v "$PWD/$BUILD_CACHE/cargo-home":/cargo-home \
  -e CARGO_TARGET_DIR=/cargo-target \
  -e CARGO_HOME=/cargo-home \
  -w /src \
  rust:1.95-bookworm \
  bash -c "set -e
    apt-get update -qq
    apt-get install -y --no-install-recommends pkg-config libssl-dev clang cmake >/dev/null
    cargo build --release --locked -p nasrudin-ga --bin worker
  "
LINUX_BIN="$BUILD_CACHE/linux-target/release/worker"
[ -f "$LINUX_BIN" ] || { echo "[worker] linux build did not produce $LINUX_BIN" >&2; exit 1; }

# ── 2. darwin arm64 (native on apple silicon) ─────────────────────────────
echo "[worker] [2/4] darwin arm64 (native)..."
rustup target list --installed | grep -q '^aarch64-apple-darwin$' \
  || rustup target add aarch64-apple-darwin
(cd engine && cargo build --release --target aarch64-apple-darwin -p nasrudin-ga --bin worker)
DARWIN_ARM_BIN=engine/target/aarch64-apple-darwin/release/worker

# ── 3. darwin x86_64 (cross from arm64; same Apple toolchain) ─────────────
DARWIN_X86_BIN=
if [ "$ENABLE_DARWIN_X86" = "1" ]; then
  echo "[worker] [3/4] darwin x86_64 (cross)..."
  rustup target list --installed | grep -q '^x86_64-apple-darwin$' \
    || rustup target add x86_64-apple-darwin
  (cd engine && cargo build --release --target x86_64-apple-darwin -p nasrudin-ga --bin worker)
  DARWIN_X86_BIN=engine/target/x86_64-apple-darwin/release/worker
else
  echo "[worker] [3/4] darwin x86_64 SKIPPED (ENABLE_DARWIN_X86=0)"
fi

# ── 4. windows x86_64 (cross via mingw-w64) ──────────────────────────────
WIN_BIN=
if [ "$ENABLE_WIN" = "1" ]; then
  if ! command -v x86_64-w64-mingw32-gcc >/dev/null 2>&1; then
    echo "[worker] [4/4] windows x86_64 SKIPPED — mingw-w64 not on PATH"
    echo "[worker]   install with:  brew install mingw-w64"
  else
    echo "[worker] [4/4] windows x86_64 (cross via mingw-w64)..."
    rustup target list --installed | grep -q '^x86_64-pc-windows-gnu$' \
      || rustup target add x86_64-pc-windows-gnu
    (cd engine && \
      CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER=x86_64-w64-mingw32-gcc \
      cargo build --release --target x86_64-pc-windows-gnu -p nasrudin-ga --bin worker)
    WIN_BIN=engine/target/x86_64-pc-windows-gnu/release/worker.exe
  fi
else
  echo "[worker] [4/4] windows x86_64 SKIPPED (ENABLE_WIN=0)"
fi

# ── stage + bundle helpers ────────────────────────────────────────────────
stage_tarball() {
  local label=$1 bin=$2
  local pkg="nasrudin-worker-${label}"
  local out="$OUT_DIR/$pkg"
  rm -rf "$out"
  mkdir -p "$out/prover"
  cp "$bin" "$out/nasrudin-worker"
  cp -R prover/PhysicsGenerator "$out/prover/"
  cp prover/PhysicsGenerator.lean prover/lakefile.lean prover/lake-manifest.json prover/lean-toolchain "$out/prover/"
  cp deploy/worker-bundle/README.md "$out/README.md"
  cp deploy/worker-bundle/run.sh "$out/run.sh"
  chmod +x "$out/run.sh" "$out/nasrudin-worker"
  (cd "$OUT_DIR" && COPYFILE_DISABLE=1 tar czf "${pkg}.tar.gz" "${pkg}")
  (cd "$OUT_DIR" && shasum -a 256 "${pkg}.tar.gz" > "${pkg}.tar.gz.sha256")
  rm -rf "$out"
}
stage_zip() {
  local label=$1 bin=$2
  local pkg="nasrudin-worker-${label}"
  local out="$OUT_DIR/$pkg"
  rm -rf "$out"
  mkdir -p "$out/prover"
  cp "$bin" "$out/nasrudin-worker.exe"
  cp -R prover/PhysicsGenerator "$out/prover/"
  cp prover/PhysicsGenerator.lean prover/lakefile.lean prover/lake-manifest.json prover/lean-toolchain "$out/prover/"
  cp deploy/worker-bundle/README.md "$out/README.md"
  cp deploy/worker-bundle/run.ps1 "$out/run.ps1"
  (cd "$OUT_DIR" && zip -qr "${pkg}.zip" "${pkg}")
  (cd "$OUT_DIR" && shasum -a 256 "${pkg}.zip" > "${pkg}.zip.sha256")
  rm -rf "$out"
}

echo "[worker] bundling..."
stage_tarball "linux-x86_64"  "$LINUX_BIN"
stage_tarball "darwin-arm64"  "$DARWIN_ARM_BIN"
[ -n "$DARWIN_X86_BIN" ] && stage_tarball "darwin-x86_64" "$DARWIN_X86_BIN"
[ -n "$WIN_BIN" ]        && stage_zip      "windows-x86_64" "$WIN_BIN"

echo
echo "[worker] artifacts in $OUT_DIR/:"
(cd "$OUT_DIR" && ls -lh *.tar.gz *.zip 2>/dev/null)
