# syntax=docker/dockerfile:1.7

# ──────────────────────────────────────────────────────────────────────────
# Build stage: cargo build --release of physics-api + discover_emc2 +
#              backfill_existing_lean + migrate
#
# Build context is the monorepo root (deploy/docker-compose.yml uses
# `context: ..`), so the Cargo workspace at `engine/` is visible.
# ──────────────────────────────────────────────────────────────────────────
FROM rust:1.93-bookworm AS builder

RUN apt-get update && apt-get install -y --no-install-recommends \
        pkg-config libssl-dev clang cmake \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /src
COPY engine engine

WORKDIR /src/engine
RUN cargo build --release \
        --bin physics-api \
        --bin discover_emc2 \
        --bin backfill_existing_lean \
        --bin migrate

# ──────────────────────────────────────────────────────────────────────────
# Runtime: minimal Debian for the API binary
# ──────────────────────────────────────────────────────────────────────────
FROM debian:bookworm-slim AS runtime

RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates curl libssl3 \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /src/engine/target/release/physics-api              /usr/local/bin/physics-api
COPY --from=builder /src/engine/target/release/migrate                  /usr/local/bin/migrate
COPY --from=builder /src/engine/target/release/backfill_existing_lean   /usr/local/bin/backfill_existing_lean

EXPOSE 3001
CMD ["/usr/local/bin/physics-api"]

# ──────────────────────────────────────────────────────────────────────────
# Worker target: same as runtime + Lean toolchain (elan) + discover_emc2
# Used by the `ga-worker` service in docker-compose.
# ──────────────────────────────────────────────────────────────────────────
FROM runtime AS worker

COPY --from=builder /src/engine/target/release/discover_emc2 /usr/local/bin/discover_emc2

# Install elan (Lean version manager) with the toolchain pinned in
# prover/lean-toolchain (currently leanprover/lean4:v4.27.0).
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --default-toolchain leanprover/lean4:v4.27.0
ENV PATH="/root/.elan/bin:${PATH}"

CMD ["/usr/local/bin/discover_emc2", "--max-lake=15"]
