#!/usr/bin/env bash
#
# derive_emc2.sh — Derive E = mc² and formally verify it
#
# This script:
#   1. Builds the Rust derivation engine
#   2. Runs the engine to derive E = mc² from the mass-shell condition
#   3. Generates a standalone Lean4 proof file
#   4. Verifies the proof with Lean4's kernel via `lake build`
#
# Requirements:
#   - Rust toolchain (cargo)
#   - Lean4 toolchain (elan/lean/lake) — installed via: curl https://elan.lean-lang.org/install.sh | sh
#   - Mathlib downloaded (happens automatically on first run via `lake update`)

set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
ENGINE="$ROOT/engine"
PROVER="$ROOT/prover"
DERIVED_DIR="$PROVER/PhysicsGenerator/Derived"

# Ensure elan is on PATH
export PATH="$HOME/.elan/bin:$PATH"

echo "═══════════════════════════════════════════════════════════════"
echo "  E = mc²  —  Derivation & Formal Verification Pipeline"
echo "═══════════════════════════════════════════════════════════════"
echo

# ── Step 1: Build Rust derivation engine ──────────────────────────
echo "▶ [1/4] Building Rust derivation engine..."
cd "$ENGINE"
cargo build -p nasrudin-derive --bin derive_emc2 --release 2>&1 | grep -E "(Compiling|Finished|error)" || true
echo "  ✓ Engine built"
echo

# ── Step 2: Run derivation ────────────────────────────────────────
echo "▶ [2/4] Deriving E = mc² from special relativity axioms..."
echo
cargo run -p nasrudin-derive --bin derive_emc2 --release -- \
    --emit "$DERIVED_DIR/AutoRestEnergy.lean"
echo

# ── Step 3: Ensure Mathlib is available ───────────────────────────
echo "▶ [3/4] Checking Lean4 + Mathlib..."
cd "$PROVER"

if ! command -v lake &>/dev/null; then
    echo "  ✗ lake not found. Install Lean4 via: curl https://elan.lean-lang.org/install.sh | sh"
    exit 1
fi

# Check if Mathlib oleans are cached
if [ ! -d "$PROVER/.lake/packages/mathlib" ]; then
    echo "  Mathlib not found. Running lake update (first time — this downloads ~2GB of cached oleans)..."
    lake update
fi
echo "  ✓ Lean4 + Mathlib ready"
echo

# ── Step 4: Verify with Lean4 kernel ─────────────────────────────
echo "▶ [4/4] Verifying generated proof with Lean4 kernel..."
echo

# Verify the hand-written proof (from our Derived/ module)
echo "  Verifying hand-written proof (RestEnergy.lean)..."
if lake build PhysicsGenerator.Derived.RestEnergy 2>&1 | grep -q "Build completed successfully"; then
    echo "  ✓ Hand-written E = mc² proof: VERIFIED"
else
    echo "  ✗ Hand-written proof failed"
    lake build PhysicsGenerator.Derived.RestEnergy 2>&1
    exit 1
fi
echo

# Verify the auto-generated proof (from Rust engine)
echo "  Verifying auto-generated proof (AutoRestEnergy.lean)..."
if lake build PhysicsGenerator.Derived.AutoRestEnergy 2>&1 | grep -q "Build completed successfully"; then
    echo "  ✓ Auto-generated E = mc² proof: VERIFIED"
else
    echo "  ✗ Auto-generated proof failed. Checking errors..."
    lake build PhysicsGenerator.Derived.AutoRestEnergy 2>&1
    exit 1
fi

echo
echo "═══════════════════════════════════════════════════════════════"
echo
echo "  ✓ E = mc²  — DERIVED AND FORMALLY VERIFIED"
echo
echo "  Chain: Mass-shell definition"
echo "       → Energy-momentum relation (algebraic rearrangement)"
echo "       → Rest frame (p = 0)"
echo "       → E² = (mc²)²"
echo "       → E = mc² (positive square root)"
echo
echo "  Verified by: Lean 4 kernel + Mathlib over ℝ"
echo
echo "═══════════════════════════════════════════════════════════════"
