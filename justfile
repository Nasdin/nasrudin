# Physics Generator - Top-level task runner
# Usage: just <recipe>

# Default recipe: show available commands
default:
    @just --list

# ── Development ──────────────────────────────────────────

# Start all services for development
dev: dev-frontend

# Start frontend dev server
dev-frontend:
    cd nasrudin-frontend && pnpm dev

# Start API server + GA engine daemon
dev-engine:
    cd engine && PROVER_ROOT=../prover cargo run --release --bin physics-api

# ── Build ────────────────────────────────────────────────

# Build everything
build: build-frontend build-engine cache-prover build-prover

# Build frontend
build-frontend:
    cd nasrudin-frontend && pnpm build

# Build Rust engine
build-engine:
    cd engine && cargo build --release

# Build Lean4 prover
build-prover:
    cd prover && lake build

# ── Test ─────────────────────────────────────────────────

# Run all tests
test: test-frontend test-engine

# Test frontend
test-frontend:
    cd nasrudin-frontend && pnpm test

# Test Rust engine
test-engine:
    cd engine && cargo test

# ── Lint & Format ────────────────────────────────────────

# Check all code
check: check-frontend check-engine

# Check frontend
check-frontend:
    cd nasrudin-frontend && pnpm check

# Check Rust engine
check-engine:
    cd engine && cargo clippy --all-targets -- -D warnings
    cd engine && cargo fmt --check

# Format all code
fmt:
    cd nasrudin-frontend && pnpm format
    cd engine && cargo fmt

# ── Database ─────────────────────────────────────────────

# Start PostgreSQL (via docker compose)
db-start:
    docker compose up -d postgres

# Stop PostgreSQL
db-stop:
    docker compose down

# Show database logs
db-logs:
    docker compose logs -f postgres

# Run database migrations
db-migrate:
    cd engine && cargo run --bin migrate

# ── PhysLean Pipeline ──────────────────────────────────────

# Fetch latest Mathlib cache for physlean-extract (saves hours of compilation)
cache-physlean:
    cd physlean-extract && lake exe cache get

# Fetch Mathlib cache for prover
cache-prover:
    cd prover && lake exe cache get

# Build the PhysLean extraction tool binary
build-extract:
    cd physlean-extract && lake build extract

# Extract theorems from PhysLean (builds extract binary first)
extract-physlean: build-extract
    cd physlean-extract && lake exe extract

# Generate .lean axiom files from PhysLean catalog
generate-axioms:
    cd engine && cargo run --release --bin generate_lean -- \
        --catalog ../physlean-extract/output/catalog.json \
        --output ../prover/PhysicsGenerator/Generated/

# Full pipeline: extract → generate → build prover
refresh-axioms: extract-physlean generate-axioms
    cd prover && lake build

# ── Utilities ────────────────────────────────────────────

# Generate TypeScript types from Rust (via specta)
gen-types:
    cd engine && cargo run --bin gen-types
    cp engine/generated/types.ts nasrudin-frontend/src/lib/generated-types.ts

# Clean all build artifacts
clean:
    cd nasrudin-frontend && rm -rf dist .output node_modules/.vite
    cd engine && cargo clean
    cd prover && lake clean
    cd physlean-extract && lake clean

# ── Continuous Operation ───────────────────────────────────

# Update PhysLean to a specific version (e.g., just update-physlean v4.27.0)
update-physlean version:
    @echo "Updating PhysLean to {{version}}..."
    cd physlean-extract && sed -i '' 's|@ "v[0-9.]*"|@ "{{version}}"|' lakefile.lean
    cd physlean-extract && sed -i '' 's|leanprover/lean4:v[0-9.]*|leanprover/lean4:{{version}}|' lean-toolchain
    cd physlean-extract && lake update
    cd physlean-extract && lake exe cache get

# Run the discovery daemon (API + GA engine) in foreground
run:
    cd engine && PROVER_ROOT=../prover cargo run --release --bin physics-api

# Full setup for a fresh VM: cache → build → run
vm-setup: cache-physlean cache-prover build-extract build-engine build-prover

# Periodic refresh: re-extract PhysLean and rebuild (for cron)
# Usage: add to crontab: 0 3 * * 0 cd /path/to/project && just cron-refresh
cron-refresh:
    #!/usr/bin/env bash
    set -euo pipefail
    LOG="logs/refresh-$(date +%Y%m%d-%H%M%S).log"
    mkdir -p logs
    echo "=== PhysLean refresh started at $(date) ===" | tee "$LOG"
    just extract-physlean 2>&1 | tee -a "$LOG"
    just generate-axioms 2>&1 | tee -a "$LOG"
    cd prover && lake build 2>&1 | tee -a "$LOG"
    echo "=== Refresh complete at $(date). Restart engine to load new axioms. ===" | tee "$LOG"

# Show extraction stats
stats:
    @python3 -c "import json; \
        cat=json.load(open('physlean-extract/output/catalog.json')); \
        print(f'PhysLean {cat[\"physlean_version\"]}: {len(cat[\"theorems\"])} theorems, {len(cat[\"types\"])} types'); \
        reax=sum(1 for t in cat['theorems'] if t['can_reaxiomatize']); \
        print(f'Re-axiomatizable: {reax}/{len(cat[\"theorems\"])}'); \
        from collections import Counter; \
        d=Counter(t['domain'] for t in cat['theorems']); \
        [print(f'  {k}: {v}') for k,v in sorted(d.items(), key=lambda x:-x[1])]"
