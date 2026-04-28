# syntax=docker/dockerfile:1.7

# ──────────────────────────────────────────────────────────────────────────
# Build stage: TanStack Start production bundle
#
# Build context is `../nasrudin-frontend` (compose-relative), so the
# frontend package is the entire context here.
# ──────────────────────────────────────────────────────────────────────────
FROM node:22-bookworm-slim AS builder

RUN corepack enable

WORKDIR /src

# Lockfile + manifest first so npm/pnpm cache layer can be reused.
COPY package.json ./
COPY pnpm-lock.yaml* ./

# pnpm-workspace.yaml is optional — only present in monorepo setups.
# Use a wildcard so the COPY is a no-op if the file is absent.
COPY pnpm-workspace.yaml* ./

# Install with frozen lockfile when present, otherwise fall back to a
# normal install (e.g. local dev where the lockfile lives at the repo root).
RUN if [ -f pnpm-lock.yaml ]; then \
        pnpm install --frozen-lockfile; \
    else \
        pnpm install; \
    fi

COPY . .

RUN pnpm build

# ──────────────────────────────────────────────────────────────────────────
# Runtime: node + the SSR server entry produced by `vite build`
#
# TanStack Start with `preset: 'node-server'` (see app.config.ts) emits its
# server bundle to `dist/server/ssr.js` and client assets to `dist/client/`.
# ──────────────────────────────────────────────────────────────────────────
FROM node:22-bookworm-slim AS runtime

WORKDIR /app

COPY --from=builder /src/dist ./dist
COPY --from=builder /src/package.json ./package.json

EXPOSE 3000
CMD ["node", "dist/server/ssr.js"]
