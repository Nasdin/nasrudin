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
build: build-frontend build-engine build-prover

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
