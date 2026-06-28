# Physics Generator - Top-level task runner
# Usage: just <recipe>

# Default recipe: show available commands
default:
    @just --list

# ── Development ──────────────────────────────────────────

# Run the whole stack locally: postgres + migrations + API + frontend + worker (Ctrl+C tears it down)
up:
    #!/usr/bin/env bash
    set -euo pipefail
    cd {{justfile_directory()}}
    if [ ! -f .env ]; then
      echo "[up] copying .env.example -> .env"
      cp .env.example .env
    fi
    set -a; . .env; set +a
    export LLM_STEER_INTERVAL_SECONDS="${LLM_STEER_INTERVAL_SECONDS:-7200}"
    export LLM_STEER_MAX_TOTAL_TOKENS="${LLM_STEER_MAX_TOTAL_TOKENS:-10000}"
    export LLM_STEER_MAX_COMPLETION_TOKENS="${LLM_STEER_MAX_COMPLETION_TOKENS:-2048}"
    export LLM_NAMING_ENABLED="${LLM_NAMING_ENABLED:-0}"
    export NASRUDIN_NO_PAID_JOBS="${NASRUDIN_NO_PAID_JOBS:-1}"
    export NASRUDIN_AUTO_TARGETS="${NASRUDIN_AUTO_TARGETS:-1}"
    export NASRUDIN_WORKER_DOMAIN="${NASRUDIN_WORKER_DOMAIN:-all}"
    export NASRUDIN_RL_HALF_LIFE_HOURS="${NASRUDIN_RL_HALF_LIFE_HOURS:-168}"
    API_PORT="${API_PORT:-3001}"
    echo "[up] laptop-origin mode: Cloudflare should route nasrudin.org -> localhost:3000 and api.nasrudin.org -> localhost:${API_PORT}"
    echo "[up] low-LLM defaults: strategy_interval=${LLM_STEER_INTERVAL_SECONDS}s max_total_tokens=${LLM_STEER_MAX_TOTAL_TOKENS} naming=${LLM_NAMING_ENABLED} no_paid_jobs=${NASRUDIN_NO_PAID_JOBS} auto_targets=${NASRUDIN_AUTO_TARGETS} worker_domain=${NASRUDIN_WORKER_DOMAIN}"
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
    # Mint a local worker bearer key on every boot. The token is DB-backed,
    # so a stale .env value after a local Postgres reset causes 401s on
    # /api/ingest even though NASRUDIN_WORKER_KEY is present. Re-issuing is
    # cheap and keeps laptop-origin mode fully automatic.
    echo "[up] minting local worker key..."
    key=$(cd engine && cargo run --release --quiet --bin issue_worker_key -- local-dev-worker | tail -n 1)
    if grep -q '^NASRUDIN_WORKER_KEY=' .env; then
      tmp=$(mktemp)
      sed "s|^NASRUDIN_WORKER_KEY=.*|NASRUDIN_WORKER_KEY=${key}|" .env > "$tmp"
      mv "$tmp" .env
    else
      printf 'NASRUDIN_WORKER_KEY=%s\n' "$key" >> .env
    fi
    export NASRUDIN_WORKER_KEY="$key"
    echo "[up] building worker binary..."
    (cd engine && cargo build --release --quiet -p nasrudin-ga --bin worker)
    echo "[up] launching api + frontend + worker (Ctrl+C to stop all)"
    trap 'kill 0 2>/dev/null || true; docker compose stop postgres >/dev/null 2>&1 || true; exit 0' INT TERM
    (cd engine && PROVER_ROOT=../prover RUST_LOG="${RUST_LOG:-info}" cargo run --release --bin physics-api 2>&1 | sed -u 's/^/[api] /') &
    (cd nasrudin-frontend && pnpm dev 2>&1 | sed -u 's/^/[web] /') &
    # Worker hydrates its corpus from /api/seed at boot — wait for the
    # API to be healthy before spawning it, otherwise the first hydrate
    # request crashes the worker process.
    echo "[up] waiting for api on :${API_PORT}..."
    for i in $(seq 1 180); do
      if curl -fsS "http://localhost:${API_PORT}/api/health" >/dev/null 2>&1; then
        echo "[up] api is healthy"
        break
      fi
      sleep 1
    done
    (cd engine && PATH="$HOME/.elan/bin:$PATH" \
      NASRUDIN_API_URL="http://localhost:${API_PORT}" \
      NASRUDIN_WORKER_ID="local-dev-worker" \
      NASRUDIN_NO_PAID_JOBS="${NASRUDIN_NO_PAID_JOBS}" \
      NASRUDIN_AUTO_TARGETS="${NASRUDIN_AUTO_TARGETS}" \
      ./target/release/worker --domain "${NASRUDIN_WORKER_DOMAIN}" --target auto --verify ../prover 2>&1 \
      | sed -u 's/^/[worker] /') &
    wait

# Print the local laptop-origin deployment checklist without starting services.
local-origin-check:
    #!/usr/bin/env bash
    set -euo pipefail
    cd {{justfile_directory()}}
    echo "Nasrudin local-origin checklist"
    echo
    echo "Expected local services:"
    echo "  frontend: http://localhost:3000"
    echo "  api:      http://localhost:${API_PORT:-3001}"
    echo
    echo "Expected Cloudflare Tunnel routes:"
    echo "  nasrudin.org     -> http://localhost:3000"
    echo "  api.nasrudin.org -> http://localhost:${API_PORT:-3001}"
    echo
    echo "Local worker defaults from just up:"
    echo "  LLM_STEER_INTERVAL_SECONDS=${LLM_STEER_INTERVAL_SECONDS:-7200}"
    echo "  LLM_STEER_MAX_TOTAL_TOKENS=${LLM_STEER_MAX_TOTAL_TOKENS:-10000}"
    echo "  LLM_NAMING_ENABLED=${LLM_NAMING_ENABLED:-0}"
    echo "  NASRUDIN_NO_PAID_JOBS=${NASRUDIN_NO_PAID_JOBS:-1}"
    echo "  NASRUDIN_AUTO_TARGETS=${NASRUDIN_AUTO_TARGETS:-1}"
    echo "  NASRUDIN_WORKER_DOMAIN=${NASRUDIN_WORKER_DOMAIN:-all}"
    echo
    if command -v cloudflared >/dev/null 2>&1; then
      echo "cloudflared: $(cloudflared --version | head -n 1)"
    else
      echo "cloudflared: not found in PATH"
    fi
    if [ -f deploy/cloudflare-local.example.yml ]; then
      echo "tunnel template: deploy/cloudflare-local.example.yml"
    else
      echo "tunnel template: missing deploy/cloudflare-local.example.yml"
    fi
    echo
    echo "Run sequence:"
    echo "  1. just up"
    echo "  2. cloudflared tunnel run nasrudin-local"

# Start frontend dev server
dev-frontend:
    cd nasrudin-frontend && pnpm dev

# Start API server + GA engine daemon (requires `just bootstrap` first)
dev-engine:
    @test -f physlean-extract/output/math_corpus.json \
        || (echo "error: math_corpus.json missing — run 'just bootstrap' first" >&2; exit 1)
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

# Extract the full Mathlib + PhysLean corpus to math_corpus.json. The
# universal Lean→Expr translator emits a structured AST for every
# walked theorem (curried `App` chains for unknown heads), so the GA
# gets the full corpus as building blocks rather than a hand-curated
# subset. `+all` skips the namespace-prefix filter entirely and relies
# on the global skip-list (Lean.*, Std.*, Mathlib.Tactic.*, _private.*,
# Aesop.*, etc.). Yields ~200k theorems, ~290 MB JSON, ~5–10 min walk.
#
# This is the right default — Mathlib's *constants* mostly live in
# bare-name namespaces (Algebra., Module., Ring., Topology.,
# Combinatorics., MeasureTheory., LinearAlgebra., Polynomial., Filter.,
# Finset., LinearMap., Submodule., InnerProductSpace., …) rather than
# under a `Mathlib.X` prefix, so the older `+mathlib` whitelist matched
# only `Real./Nat./Int./Rat./Complex.` and missed everything else.
# PhysLean must be built once via `just build-extract`.
extract-mathlib: build-extract
    cd physlean-extract && lake exe extract \
        --whitelist=+all \
        --output=output/math_corpus.json

# Narrower whitelist for development / CI when the full +all corpus
# would be too slow. Yields ~14 k theorems (Real./Nat./Int./Rat./
# Complex./physics-namespaces). Not recommended for production: misses
# 90+% of Mathlib's algebraic/topological/probability content.
extract-mathlib-narrow: build-extract
    cd physlean-extract && lake exe extract \
        --whitelist=+phys,+mathlib \
        --output=output/math_corpus.json

# Pull latest PhysLean + Mathlib upstreams, rebuild the dependency
# closure, re-extract BOTH the PhysLean catalog (load-from-catalog) AND
# the full Mathlib corpus (load-math-corpus), then hot-reload the live
# API. New upstream theorems flow into the GA's `IntroduceTheorem`
# candidate pool without an API redeploy.
#
# Set `ADMIN_TOKEN` and `API_URL` in the environment (defaults to
# localhost:3001). Hot-reload is best-effort — the recipe still
# completes if the API is offline.
#
# This is the one-command path for "I want the latest from upstream".
# Run periodically (weekly?) to track Mathlib + PhysLean evolution.
refresh-corpus:
    @echo "[refresh-corpus] pulling latest PhysLean + Mathlib..."
    cd physlean-extract && lake update PhysLean
    cd physlean-extract && lake build PhysLean
    @echo "[refresh-corpus] re-extracting PhysLean catalog..."
    just extract-physlean
    @echo "[refresh-corpus] re-extracting full Mathlib corpus (~5–10 min)..."
    just extract-mathlib
    @echo "[refresh-corpus] hot-reloading live API AxiomStore..."
    @curl -fsS -X POST \
        -H "Authorization: Bearer $${ADMIN_TOKEN:-changeme}" \
        "$${API_URL:-http://localhost:3001}/api/admin/reload_corpus" \
        | python3 -m json.tool || echo "(reload skipped — API not running or token wrong)"
    @echo "[refresh-corpus] done. catalog + math_corpus now reflect upstream HEAD."

# Update only the Mathlib + PhysLean sources (no extraction). Useful
# when CI / a deploy job will run extraction itself. Same as the first
# two steps of refresh-corpus.
update-upstreams:
    cd physlean-extract && lake update PhysLean
    cd physlean-extract && lake build PhysLean

# Generate .lean axiom files from PhysLean catalog
generate-axioms:
    cd engine && cargo run --release --bin generate_lean -- \
        --catalog ../physlean-extract/output/catalog.json \
        --output ../prover/PhysicsGenerator/Generated/

# Full pipeline: extract → generate → build prover
refresh-axioms: extract-physlean generate-axioms
    cd prover && lake build

# Full bootstrap: extract PhysLean + Mathlib, generate axioms, build prover.
# Required before first `just dev-engine` / `just up` — Mathlib is now a
# hard requirement at API boot (≥10k entries; physics-api panics otherwise).
bootstrap: extract-physlean extract-mathlib generate-axioms
    cd prover && lake build
    @echo "[bootstrap] complete. Run 'just up' or 'just dev-engine'."

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

# Local verification-only smoke for the GA workhorse path. No API key,
# no server submission, no paid theorem-naming jobs. Expected result:
# one Lake attempt, one Lake pass, and the spontaneous E=mc² banner.
smoke-emc2-local:
    cd engine && PATH="$HOME/.elan/bin:$PATH" NASRUDIN_NO_PAID_JOBS=1 cargo run -p nasrudin-ga --bin worker -- \
        --domain sr --target sr_rest_energy \
        --verify ../prover \
        --gens 1 --pop 8 --chunks 1 --max-lake 1 \
        --no-persistent-elaborator \
        --no-submit \
        --submit-top-k 0

# Local verification-only quantum smoke. Same low-cost constraints as
# smoke-emc2-local, but runs the QM island against the Planck-Einstein
# target and verifies the generated theorem locally.
smoke-qm-local:
    cd engine && PATH="$HOME/.elan/bin:$PATH" NASRUDIN_NO_PAID_JOBS=1 cargo run -p nasrudin-ga --bin worker -- \
        --domain qm --target qm_planck_einstein \
        --verify ../prover \
        --gens 1 --pop 8 --chunks 1 --max-lake 1 \
        --no-persistent-elaborator \
        --no-submit \
        --submit-top-k 0

# Local verification-only auto-target smoke. Uses an isolated temporary
# worker RL state file so the test proves cold-start target-portfolio
# selection instead of inheriting this machine's learned history.
smoke-auto-qm-local:
    tmp="$$(mktemp -d)" && cd engine && PATH="$HOME/.elan/bin:$PATH" NASRUDIN_NO_PAID_JOBS=1 NASRUDIN_WORKER_RL_STATE="$$tmp/worker_rl_state.json" cargo run -p nasrudin-ga --bin worker -- \
        --domain qm --target auto \
        --verify ../prover \
        --gens 1 --pop 8 --chunks 1 --max-lake 1 \
        --no-persistent-elaborator \
        --no-submit \
        --submit-top-k 0

# Local verification-only featured QM curriculum smoke. Uses one
# temporary worker RL state across two auto-target runs: first proves
# Planck-Einstein, persists it as proved, then the second run should
# advance to the next featured QM target (Schrödinger) and verify it.
smoke-featured-qm-local:
    tmp="$$(mktemp -d)" && cd engine && PATH="$HOME/.elan/bin:$PATH" NASRUDIN_NO_PAID_JOBS=1 NASRUDIN_WORKER_RL_STATE="$$tmp/worker_rl_state.json" cargo run -p nasrudin-ga --bin worker -- \
        --domain qm --target auto \
        --verify ../prover \
        --gens 1 --pop 8 --chunks 1 --max-lake 1 \
        --no-persistent-elaborator \
        --no-submit \
        --submit-top-k 0 && \
    PATH="$HOME/.elan/bin:$PATH" NASRUDIN_NO_PAID_JOBS=1 NASRUDIN_WORKER_RL_STATE="$$tmp/worker_rl_state.json" cargo run -p nasrudin-ga --bin worker -- \
        --domain qm --target auto \
        --verify ../prover \
        --gens 1 --pop 8 --chunks 1 --max-lake 1 \
        --no-persistent-elaborator \
        --no-submit \
        --submit-top-k 0

# Local verification-only all-domain featured curriculum smoke. Mirrors
# the default worker mode in `just up` (`--domain all --target auto`):
# first prove E=mc², persist it as proved, then advance to the next
# featured target in the global curriculum.
smoke-featured-all-local:
    tmp="$$(mktemp -d)" && cd engine && PATH="$HOME/.elan/bin:$PATH" NASRUDIN_NO_PAID_JOBS=1 NASRUDIN_WORKER_RL_STATE="$$tmp/worker_rl_state.json" cargo run -p nasrudin-ga --bin worker -- \
        --domain all --target auto \
        --verify ../prover \
        --gens 1 --pop 8 --chunks 1 --max-lake 1 \
        --no-persistent-elaborator \
        --no-submit \
        --submit-top-k 0 && \
    PATH="$HOME/.elan/bin:$PATH" NASRUDIN_NO_PAID_JOBS=1 NASRUDIN_WORKER_RL_STATE="$$tmp/worker_rl_state.json" cargo run -p nasrudin-ga --bin worker -- \
        --domain all --target auto \
        --verify ../prover \
        --gens 1 --pop 8 --chunks 1 --max-lake 1 \
        --no-persistent-elaborator \
        --no-submit \
        --submit-top-k 0

# Run the chain-based GA discovery and lake-verify the top novel
# candidates per generation (Phase 8.2). The GA evolves chains over
# the upstream axiom set, with no DeriveRestEnergy* strategy. Verified
# discoveries land in `prover/PhysicsGenerator/Derived/DiscoverGen{n}.lean`.
discover-physics gens="100" pop="64" max-lake="12":
    @echo "═══════════════════════════════════════════════════════"
    @echo "  Nasrudin — Spontaneous physics discovery via GA"
    @echo "═══════════════════════════════════════════════════════"
    cd engine && cargo build -p nasrudin-ga --bin worker --release 2>&1 | grep -E "(Compiling|Finished|error)" || true
    cd engine && PATH="$HOME/.elan/bin:$PATH" ./target/release/worker \
        --gens {{gens}} --pop {{pop}} --max-len 14 --max-lake {{max-lake}} \
        --verify ../prover

# Spawn N parallel worker workers, each with a unique worker_id,
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
    cd engine && cargo build -p nasrudin-ga --bin worker --release 2>&1 | grep -E "(Compiling|Finished|error)" || true
    cd ..
    mkdir -p logs/pool
    pids=()
    trap 'echo; echo "[pool] tearing down workers..."; for pid in "${pids[@]}"; do kill "$pid" 2>/dev/null || true; done; wait 2>/dev/null; exit 0' INT TERM
    echo "[pool] spawning {{n}} workers against $NASRUDIN_API_URL"
    for i in $(seq 1 {{n}}); do
      LOG="logs/pool/worker-${i}.log"
      PATH="$HOME/.elan/bin:$PATH" \
        NASRUDIN_WORKER_ID="pool-worker-${i}" \
        ./engine/target/release/worker \
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

# ── Production Deploy (sgp1 droplet, native services) ──────

# Build linux/amd64 release artifact (Rust binaries + frontend + prover) → dist/release.tar.gz
build-release:
    @deploy/scripts/build-release.sh

# Deploy: build artifact + scp + run provision-native.sh on the droplet.
# Usage: just deploy ip=167.172.6.171
#        just deploy ip=167.172.6.171 stripe=~/.nasrudin-stripe.env
deploy ip stripe="":
    #!/usr/bin/env bash
    set -euo pipefail
    cd {{justfile_directory()}}
    if [ -n "{{stripe}}" ]; then
      deploy/scripts/deploy.sh "{{ip}}" "{{stripe}}"
    else
      deploy/scripts/deploy.sh "{{ip}}"
    fi

# Run the post-deploy smoke test against production URLs.
smoke-prod:
    NASRUDIN_API_PUBLIC_URL=https://api.nasrudin.org \
    NASRUDIN_FRONTEND_PUBLIC_URL=https://nasrudin.org \
    deploy/scripts/smoke.sh

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
    (cd engine && cargo build --release -p nasrudin-ga --bin worker)
    rm -rf "$OUT"
    mkdir -p "$OUT/prover"
    cp engine/target/release/worker "$OUT/nasrudin-worker"
    cp -R prover/PhysicsGenerator "$OUT/prover/"
    cp prover/PhysicsGenerator.lean prover/lakefile.lean prover/lake-manifest.json prover/lean-toolchain "$OUT/prover/"
    cp deploy/worker-bundle/README.md "$OUT/README.md"
    cp deploy/worker-bundle/run.sh "$OUT/run.sh"
    chmod +x "$OUT/run.sh" "$OUT/nasrudin-worker"
    (cd dist && tar czf "${PKG}.tar.gz" "${PKG}")
    echo "[worker] -> dist/${PKG}.tar.gz"

# Cross-compile worker for linux/darwin/windows + bundle (no GH Actions; all local)
build-worker-all:
    @deploy/scripts/build-worker-all.sh

# Tag a worker release `vX.Y.Z`: AI-summarize commits, build all platforms locally,
# create GitHub release with the binaries attached. No GH Actions.
release-worker version:
    #!/usr/bin/env bash
    set -euo pipefail
    cd {{justfile_directory()}}
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
    if ! command -v claude >/dev/null 2>&1; then
      echo "error: 'claude' CLI not found on PATH" >&2
      echo "  install: npm i -g @anthropic-ai/claude-code" >&2
      exit 1
    fi

    git fetch --tags origin >/dev/null 2>&1 || true

    PREV_TAG="$(git tag -l 'worker-v*' --sort=-v:refname | head -n 1 || true)"
    if [ -z "$PREV_TAG" ]; then
      RANGE="HEAD"
      RANGE_LABEL="initial release (full history)"
    else
      RANGE="${PREV_TAG}..HEAD"
      RANGE_LABEL="${PREV_TAG} → ${TAG}"
    fi

    LOG_FILE="$(mktemp)"
    NOTES_FILE="$(mktemp)"
    trap 'rm -f "$LOG_FILE" "$NOTES_FILE"' EXIT

    git log "$RANGE" --no-merges --pretty=format:'- %h %s%n%b' > "$LOG_FILE"
    if [ ! -s "$LOG_FILE" ]; then
      echo "error: no commits since ${PREV_TAG:-repository start}" >&2
      exit 1
    fi

    COMMIT_COUNT=$(git rev-list --no-merges --count "$RANGE")
    echo "[release] summarizing ${COMMIT_COUNT} commits (${RANGE_LABEL}) via claude code..."

    # Pipe prompt + git log via stdin: --disallowed-tools is variadic in
    # commander.js and would otherwise eat the positional prompt argument.
    {
      cat <<EOF
    Write GitHub release notes for the Nasrudin discovery worker — a Rust
    binary that contributes compute to a centralized physics-derivation
    system. Audience: developers who downloaded a prior worker release.

    Style rules:
    - Plain GitHub-flavored markdown. No preamble, no closing sign-off, no emoji.
    - Group by theme: ### Features / ### Fixes / ### Performance / ### Internal.
      Only include sections that have entries.
    - Bullet points are short, written in past tense, and reference user-visible
      behavior — not commit hashes or file paths.
    - Skip merge commits, version bumps, dependency-only churn, and generated-file noise.
    - End with one blank line, then a single line: "**Install:** download the
      bundle for your platform below, extract, and follow \`README.md\`."
    - Total length under 250 words.

    Range: ${RANGE_LABEL}
    Commits:

    EOF
      cat "$LOG_FILE"
    } | claude -p \
        --no-session-persistence \
        --output-format text \
        --disallowed-tools "Bash Edit Write Glob Grep Read WebFetch WebSearch Agent NotebookEdit" \
        > "$NOTES_FILE"

    if [ ! -s "$NOTES_FILE" ]; then
      echo "error: claude returned empty release notes" >&2
      exit 1
    fi

    echo
    echo "═════════════════ release notes ($TAG) ═════════════════"
    cat "$NOTES_FILE"
    echo
    echo "═════════════════════════════════════════════════════════"
    echo

    if [ -t 0 ]; then
      read -r -p "[release] tag $TAG, build all platforms locally, and publish to GitHub? [y/N] " confirm
    else
      confirm="n"
    fi
    case "$confirm" in
      y|Y|yes|YES) ;;
      *) echo "[release] aborted (no tag created)"; exit 1 ;;
    esac

    if ! command -v gh >/dev/null 2>&1; then
      echo "error: 'gh' CLI required for local publish (brew install gh)" >&2
      exit 1
    fi

    echo "[release] cross-compiling worker for linux/darwin/windows..."
    deploy/scripts/build-worker-all.sh

    echo "[release] creating annotated tag $TAG"
    git tag -a "$TAG" -F "$NOTES_FILE"
    git push origin "$TAG"

    echo "[release] uploading bundles to GitHub release $TAG"
    shopt -s nullglob
    files=( dist/worker-release/*.tar.gz dist/worker-release/*.zip dist/worker-release/*.sha256 )
    if [ "${#files[@]}" -eq 0 ]; then
      echo "error: no artifacts in dist/worker-release/" >&2
      exit 1
    fi
    VERSION="{{version}}"
    gh release create "$TAG" \
      --title "Nasrudin Worker $VERSION" \
      --notes-file "$NOTES_FILE" \
      "${files[@]}"

    echo "[release] published:"
    echo "    https://github.com/Nasdin/nasrudin/releases/tag/${TAG}"

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
