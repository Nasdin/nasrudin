# Physics Generator - Top-level task runner
# Usage: just <recipe>

# Default recipe: show available commands
default:
    @just --list

# ── Development ──────────────────────────────────────────

# Run the whole stack locally: postgres + migrations + API + frontend (Ctrl+C tears it down)
up:
    #!/usr/bin/env bash
    set -euo pipefail
    cd {{justfile_directory()}}
    if [ ! -f .env ]; then
      echo "[up] copying .env.example -> .env"
      cp .env.example .env
    fi
    set -a; . .env; set +a
    echo "[up] starting postgres..."
    docker compose up -d postgres
    echo "[up] waiting for postgres..."
    for i in $(seq 1 30); do
      if docker compose exec -T postgres pg_isready -U "$POSTGRES_USER" >/dev/null 2>&1; then
        break
      fi
      sleep 1
    done
    echo "[up] running migrations..."
    (cd engine && cargo run --quiet --bin migrate -- up)
    echo "[up] launching api + frontend (Ctrl+C to stop both)"
    trap 'kill 0 2>/dev/null || true; docker compose stop postgres >/dev/null 2>&1 || true; exit 0' INT TERM
    (cd engine && PROVER_ROOT=../prover RUST_LOG="${RUST_LOG:-info}" cargo run --release --bin physics-api 2>&1 | sed -u 's/^/[api] /') &
    (cd nasrudin-frontend && pnpm dev 2>&1 | sed -u 's/^/[web] /') &
    wait

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

# Extract a curated Mathlib subset to physlean-extract/output/math_corpus.json.
# The whitelist targets real-arithmetic identities the GA can rewrite over
# (algebra, exponent/power rules over ℝ). PhysLean must already be built
# (`just build-extract` once). The output JSON's `expr_ast` field is the
# load-bearing one — nasrudin_derive::AxiomStore only registers a real
# Expr for entries with `expr_ast != null`.
extract-mathlib: build-extract
    cd physlean-extract && lake exe extract \
        --whitelist=Mathlib.Algebra.Ring.Basic,Mathlib.Algebra.GroupPower.Basic,Mathlib.Algebra.Order.Ring,Mathlib.Data.Real.Basic,Mathlib.Analysis.SpecialFunctions.Pow.Real,Real. \
        --output=output/math_corpus.json

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

# ── Spontaneous Discovery ──────────────────────────────────

# Derive E=mc² from truly upstream SR axioms (no mass_shell_condition
# axiom; no DeriveRestEnergy strategy). Emits a Lean proof file and
# verifies it via `lake build`. The deterministic Phase 8.1 demo path:
# guaranteed to work; hand-coded DeriveRestEnergyFromUpstream strategy
# composes the upstream chain.
spontaneous-emc2:
    @echo "═══════════════════════════════════════════════════════"
    @echo "  Nasrudin — Deriving E=mc² from upstream SR axioms"
    @echo "  (no mass_shell_condition; chain primitives only)"
    @echo "═══════════════════════════════════════════════════════"
    cd engine && cargo build -p nasrudin-derive --bin derive_emc2_upstream --release 2>&1 | grep -E "(Compiling|Finished|error)" || true
    cd engine && PATH="$HOME/.elan/bin:$PATH" ./target/release/derive_emc2_upstream \
        --emit ../prover/PhysicsGenerator/Derived/AutoRestEnergyUpstream.lean \
        --verify ../prover

# Run the chain-based GA discovery and lake-verify the top novel
# candidates per generation (Phase 8.2). The GA evolves chains over
# the upstream axiom set, with no DeriveRestEnergy* strategy. Verified
# discoveries land in `prover/PhysicsGenerator/Derived/DiscoverGen{n}.lean`.
discover-physics gens="100" pop="64" max-lake="12":
    @echo "═══════════════════════════════════════════════════════"
    @echo "  Nasrudin — Spontaneous physics discovery via GA"
    @echo "═══════════════════════════════════════════════════════"
    cd engine && cargo build -p nasrudin-ga --bin discover_emc2 --release 2>&1 | grep -E "(Compiling|Finished|error)" || true
    cd engine && PATH="$HOME/.elan/bin:$PATH" ./target/release/discover_emc2 \
        --gens {{gens}} --pop {{pop}} --max-len 14 --max-lake {{max-lake}} \
        --verify ../prover

# Spawn N parallel discover_emc2 workers, each with a unique worker_id,
# all submitting to the same NASRUDIN_API_URL. Each worker has its own
# log file under logs/pool/. Ctrl+C tears them all down via trap.
#
#   just discover-pool 4
#   NASRUDIN_API_URL=http://localhost:3001 NASRUDIN_WORKER_KEY=$(cat /tmp/worker-key) just discover-pool 8
discover-pool n="4" gens="200" pop="64" max-lake="4":
    #!/usr/bin/env bash
    set -euo pipefail
    cd {{justfile_directory()}}
    if [ -z "${NASRUDIN_WORKER_KEY:-}" ]; then
      echo "error: NASRUDIN_WORKER_KEY is required" >&2
      echo "  Get a worker key at /api-keys (Kind: Worker)" >&2
      exit 1
    fi
    export NASRUDIN_API_URL="${NASRUDIN_API_URL:-http://localhost:3001}"
    cd engine && cargo build -p nasrudin-ga --bin discover_emc2 --release 2>&1 | grep -E "(Compiling|Finished|error)" || true
    cd ..
    mkdir -p logs/pool
    pids=()
    trap 'echo; echo "[pool] tearing down workers..."; for pid in "${pids[@]}"; do kill "$pid" 2>/dev/null || true; done; wait 2>/dev/null; exit 0' INT TERM
    echo "[pool] spawning {{n}} workers against $NASRUDIN_API_URL"
    for i in $(seq 1 {{n}}); do
      LOG="logs/pool/worker-${i}.log"
      PATH="$HOME/.elan/bin:$PATH" \
        NASRUDIN_WORKER_ID="pool-worker-${i}" \
        ./engine/target/release/discover_emc2 \
          --domain sr --target sr_rest_energy \
          --gens {{gens}} --pop {{pop}} --max-len 12 --max-lake {{max-lake}} \
          --verify ./prover \
          > "$LOG" 2>&1 &
      pid=$!
      pids+=("$pid")
      echo "  [pool] worker-${i} pid=${pid} log=${LOG}"
    done
    echo "[pool] {{n}} workers running. tail -f logs/pool/worker-*.log to follow."
    echo "[pool] Ctrl+C to stop all workers."
    wait

# ── Worker Binary Release ──────────────────────────────────

# Build the public discovery worker tarball for the current host (dist/nasrudin-worker-<os>-<arch>.tar.gz)
build-worker:
    #!/usr/bin/env bash
    set -euo pipefail
    cd {{justfile_directory()}}
    OS=$(uname -s | tr '[:upper:]' '[:lower:]')
    ARCH=$(uname -m)
    TAG="${OS}-${ARCH}"
    PKG="nasrudin-worker-${TAG}"
    OUT="dist/${PKG}"
    echo "[worker] building release binary for ${TAG}..."
    (cd engine && cargo build --release -p nasrudin-ga --bin discover_emc2)
    rm -rf "$OUT"
    mkdir -p "$OUT/prover"
    cp engine/target/release/discover_emc2 "$OUT/nasrudin-worker"
    cp -R prover/PhysicsGenerator "$OUT/prover/"
    cp prover/PhysicsGenerator.lean prover/lakefile.lean prover/lake-manifest.json prover/lean-toolchain "$OUT/prover/"
    cp deploy/worker-bundle/README.md "$OUT/README.md"
    cp deploy/worker-bundle/run.sh "$OUT/run.sh"
    chmod +x "$OUT/run.sh" "$OUT/nasrudin-worker"
    (cd dist && tar czf "${PKG}.tar.gz" "${PKG}")
    echo "[worker] -> dist/${PKG}.tar.gz"

# Tag a worker release (e.g. `just release-worker version=v0.1.0`); CI builds + publishes the tarballs
release-worker version:
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ ! "{{version}}" =~ ^v[0-9]+\.[0-9]+\.[0-9]+(-[a-z0-9]+)?$ ]]; then
      echo "error: version must look like vX.Y.Z (got '{{version}}')" >&2
      exit 1
    fi
    TAG="worker-{{version}}"
    if git rev-parse "$TAG" >/dev/null 2>&1; then
      echo "error: tag $TAG already exists" >&2
      exit 1
    fi
    if [ -n "$(git status --porcelain)" ]; then
      echo "error: working tree is dirty; commit first" >&2
      exit 1
    fi
    echo "[release] tagging $TAG"
    git tag -a "$TAG" -m "Worker release {{version}}"
    git push origin "$TAG"
    echo "[release] pushed; GitHub Actions will build + publish at:"
    echo "    https://github.com/nasdin/nasrudin/actions"

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
