#!/usr/bin/env bash
# Cross-compile the public discovery-worker binary for every supported
# host platform LOCALLY (no GitHub Actions, no Docker). Output:
#
#   dist/worker-release/nasrudin-worker-linux-x86_64.tar.gz
#   dist/worker-release/nasrudin-worker-linux-aarch64.tar.gz
#   dist/worker-release/nasrudin-worker-darwin-x86_64.tar.gz
#   dist/worker-release/nasrudin-worker-darwin-arm64.tar.gz
#   dist/worker-release/nasrudin-worker-windows-x86_64.zip
#   …each with a matching .sha256 sidecar.
#
# Each bundle contains: nasrudin-worker[.exe], run.sh / run.ps1,
# README.md, prover/ (source — first run executes `lake exe cache get`).
#
# Toolchain: cargo-zigbuild handles all cross targets (Linux glibc 2.17 +
# Windows MinGW); native cargo for the two macOS archs. Zig + cargo-zigbuild
# are required (`brew install zig && cargo install cargo-zigbuild`); rustup
# targets are added on demand.

set -euo pipefail
cd "$(dirname "$0")/../.."

OUT_DIR=dist/worker-release

# ── pre-flight ────────────────────────────────────────────────────────────
need() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "[worker] error: '$1' not found on PATH — $2" >&2
    exit 1
  }
}
need zig            "brew install zig"
need cargo-zigbuild "cargo install cargo-zigbuild"
need shasum         "(should ship with macOS by default)"

for T in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu \
         x86_64-apple-darwin aarch64-apple-darwin \
         x86_64-pc-windows-gnu; do
  rustup target list --installed | grep -q "^${T}$" \
    || rustup target add "$T" >/dev/null
done

echo "[worker] cleaning $OUT_DIR"
rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

# ── builders ──────────────────────────────────────────────────────────────
build_zig() {
  local rust_target=$1
  echo "[worker]   cargo zigbuild --target $rust_target"
  (cd engine && cargo zigbuild --release --target "$rust_target" -p nasrudin-ga --bin worker)
}
build_native() {
  local rust_target=$1
  echo "[worker]   cargo build --target $rust_target"
  (cd engine && cargo build --release --target "$rust_target" -p nasrudin-ga --bin worker)
}

# ── stagers ───────────────────────────────────────────────────────────────
# NOTE: zigbuild outputs to engine/target/<rustc-triple>/release/, where
# <rustc-triple> is the target without any ".glibc-VERSION" suffix.
stage_unix() {
  local label=$1 triple=$2
  local pkg="nasrudin-worker-${label}"
  local out="$OUT_DIR/$pkg"
  local bin="engine/target/${triple%.*}/release/worker"
  [ -f "$bin" ] || { echo "[worker] error: missing $bin" >&2; exit 1; }
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
  echo "[worker]   ✓ ${pkg}.tar.gz"
}
stage_windows() {
  local triple=$1
  local pkg="nasrudin-worker-windows-x86_64"
  local out="$OUT_DIR/$pkg"
  local bin="engine/target/${triple%.*}/release/worker.exe"
  [ -f "$bin" ] || { echo "[worker] error: missing $bin" >&2; exit 1; }
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
  echo "[worker]   ✓ ${pkg}.zip"
}

# ── 1. linux x86_64 (zigbuild, glibc 2.17 — broad compat) ────────────────
echo "[worker] [1/5] linux-x86_64 …"
build_zig "x86_64-unknown-linux-gnu.2.17"
stage_unix "linux-x86_64" "x86_64-unknown-linux-gnu"

# ── 2. linux aarch64 (zigbuild, glibc 2.17 — Graviton/Ampere/Pi) ─────────
echo "[worker] [2/5] linux-aarch64 …"
build_zig "aarch64-unknown-linux-gnu.2.17"
stage_unix "linux-aarch64" "aarch64-unknown-linux-gnu"

# ── 3. darwin arm64 (native on Apple Silicon) ────────────────────────────
echo "[worker] [3/5] darwin-arm64 …"
build_native "aarch64-apple-darwin"
stage_unix "darwin-arm64" "aarch64-apple-darwin"

# ── 4. darwin x86_64 (cross from arm64; same Apple toolchain) ────────────
echo "[worker] [4/5] darwin-x86_64 …"
build_native "x86_64-apple-darwin"
stage_unix "darwin-x86_64" "x86_64-apple-darwin"

# ── 5. windows x86_64 (zigbuild, MinGW ABI — no SDK needed) ──────────────
echo "[worker] [5/5] windows-x86_64 …"
build_zig "x86_64-pc-windows-gnu"
stage_windows "x86_64-pc-windows-gnu"

echo
echo "[worker] artifacts in $OUT_DIR/:"
(cd "$OUT_DIR" && ls -lh *.tar.gz *.zip 2>/dev/null)
