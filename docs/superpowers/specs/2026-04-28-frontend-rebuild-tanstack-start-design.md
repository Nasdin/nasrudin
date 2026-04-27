# Frontend rebuild on TanStack Start + platform API extension

**Date:** 2026-04-28
**Author:** Nasrudin (with Claude)
**Status:** approved (no further design questions)

## 1. Goal

Rebuild `nasrudin-frontend` from the prototype HTML/CSS/JSX mocks into a working TanStack Start v1 (React 19, Vite, TypeScript) application, and extend `engine/crates/api` with the missing platform endpoints so the new frontend has real data on every page.

Concrete acceptance criteria:

1. `pnpm dev` (or `just dev-frontend`) starts a TanStack Start dev server on `:3000` that renders all eight pages without console errors.
2. `cargo run -p physics-api` (or `just dev-engine`) starts the Axum daemon on `:3001` with the new `api_keys`, `saved_searches`, `user_preferences`, `workers` HTTP endpoints live, in addition to the already-wired auth + theorem routes.
3. With Postgres running (`just db-start`), a fresh user can: register from `/signin`, see themselves on `/profile`, generate an API key, browse the corpus on `/browse`, open a theorem detail at `/theorem/$id`, and view the contributor leaderboard at `/leaderboard`.
4. `Authorization: Bearer nsk_…` works against the same protected endpoints that cookie sessions reach. Both auth paths resolve to the same `AuthUser`.
5. `pnpm check` passes (Biome lint + `tsc --noEmit`). `cargo clippy --all-targets -- -D warnings` passes for the engine workspace.

## 2. High-level architecture

```
┌─ nasrudin-frontend (TanStack Start v1, React 19) ──────────────┐
│  src/routes/*  → file-based, SSR + hydration                    │
│  src/lib/api.ts  → fetch wrapper, credentials: "include"        │
│  src/lib/queries.ts → TanStack Query hooks                      │
│  src/styles/{tokens,styles,platform}.css → imported as-is       │
└─────────────────────────────────────────────────────────────────┘
                          │ fetch :3001/api/*
                          ▼
┌─ engine/crates/api (Axum 0.8) ─────────────────────────────────┐
│  Existing: theorems, SSE, /api/auth/{register,login,logout,me} │
│  New:      /api/api-keys/{create,list,revoke}                  │
│            /api/saved-searches/{create,list,delete,patch-label}│
│            /api/preferences (GET, PATCH)                       │
│            /api/workers/{register,heartbeat,list,me}           │
│            /api/me/stats                                       │
│  New mw:   AuthOrApiKey extractor (cookie session OR Bearer)   │
└─────────────────────────────────────────────────────────────────┘
                          │ SeaORM 2
                          ▼
┌─ Postgres 18 (docker-compose) ─────────────────────────────────┐
│  users · sessions · saved_searches · user_preferences ·        │
│  workers · api_keys (NEW)                                      │
└─────────────────────────────────────────────────────────────────┘
```

Three rules:

- **Single backend.** TanStack Start is SSR + hydration only. No server functions, no Node BFF. Every data read/write goes to the Rust API at `:3001`.
- **Single auth model.** Cookie sessions (axum-login + tower-sessions) for the web UI; `Authorization: Bearer nsk_…` for programmatic clients. Both resolve through the same `AuthOrApiKey` extractor to the same `AuthUser`. Same handlers, same rate-limit groups.
- **CSS as-is.** `tokens.css`, `styles.css`, `platform.css` are the styling source of truth. They import Google Fonts (Source Serif 4, Inter Tight, Caveat, JetBrains Mono) via `@import`. We move the files into `src/styles/` and reference them from the root layout. No Tailwind, no CSS Modules, no runtime CSS-in-JS.

## 3. Frontend package and tooling

### 3.1 Package manifest

`nasrudin-frontend/package.json`:

| Dependency | Version | Why |
|------------|---------|-----|
| `react` | `^19` | Per README. Latest stable. |
| `react-dom` | `^19` | Same. |
| `@tanstack/react-start` | `latest` | TanStack Start v1 (SSR framework). |
| `@tanstack/react-router` | `latest` | File-based router (transitive but pinned). |
| `@tanstack/router-plugin` | `latest` | Vite plugin for route generation. |
| `@tanstack/react-query` | `^5` | Data fetching + cache. |
| `@tanstack/react-query-devtools` | `^5` | Dev only. |
| `vite` | `^7` | TanStack Start v1 stable runs on Vite directly via the `@tanstack/react-start` Vite plugin. No vinxi. |
| `typescript` | `^5.9` | Latest stable. |
| `@biomejs/biome` | `^2` | Lint + format (replaces deleted `biome.json`). |
| `katex` + `react-katex` | `^0.16` / `^3` | Math rendering for theorem statements. |
| `zod` | `^3` | API response validation at the boundary. |

We resolve exact versions via `pnpm install` against the registry at implementation time (the rule is "latest stable"; the implementation plan locks the exact versions chosen and commits the `pnpm-lock.yaml`).

### 3.2 Project structure

```
nasrudin-frontend/
├── package.json
├── pnpm-lock.yaml
├── biome.json                         # lint + format
├── tsconfig.json
├── vite.config.ts                     # TanStack Start plugin + router plugin
├── app.config.ts                      # TanStack Start config (port 3000)
├── public/
│   └── pattern-geometric.svg          # moved from assets/
├── src/
│   ├── router.tsx                     # createRouter()
│   ├── ssr.tsx                        # createStartHandler entry
│   ├── client.tsx                     # hydration entry
│   ├── styles/
│   │   ├── tokens.css                 # moved verbatim
│   │   ├── styles.css                 # moved verbatim
│   │   └── platform.css               # moved verbatim
│   ├── lib/
│   │   ├── api.ts                     # apiFetch(), baseURL, error mapping
│   │   ├── queries.ts                 # useTheorems, useTheorem, useMe, etc.
│   │   ├── types.ts                   # Theorem, Domain, AuthUser, ApiKey, etc.
│   │   ├── katex.tsx                  # KaTeX react helper
│   │   └── format.ts                  # number/date formatters
│   ├── components/
│   │   ├── platform/
│   │   │   ├── AppHeader.tsx          # from platform-shell.jsx
│   │   │   ├── AppFooter.tsx          # from platform-shell.jsx
│   │   │   └── PageHead.tsx
│   │   ├── landing/
│   │   │   ├── HeroLiveTheorem.tsx    # from hero.jsx (live ticker via SSE)
│   │   │   ├── PipelineDiagram.tsx    # from sections.jsx
│   │   │   ├── GAViz.tsx              # from sections.jsx
│   │   │   ├── WorkerMap.tsx          # from sections.jsx
│   │   │   ├── TheoremBrowser.tsx     # from sections.jsx (mini-browser)
│   │   │   └── InstallNode.tsx        # from sections.jsx
│   │   ├── theorem/
│   │   │   ├── TheoremCard.tsx
│   │   │   ├── ProofBlock.tsx         # KaTeX + syntax-highlit Lean
│   │   │   ├── LineageList.tsx
│   │   │   └── ReverifyButton.tsx
│   │   ├── browse/
│   │   │   ├── FacetSidebar.tsx
│   │   │   └── ResultCard.tsx
│   │   ├── auth/
│   │   │   └── AuthForm.tsx           # signin / signup tabs
│   │   ├── apikeys/
│   │   │   ├── ApiKeyList.tsx
│   │   │   └── CreateKeyDialog.tsx    # one-time-reveal modal
│   │   └── pricing/
│   │       └── TierCard.tsx
│   └── routes/                        # file-based routes
│       ├── __root.tsx                 # CSS imports, QueryProvider, error/not-found
│       ├── index.tsx                  # Nasrudin Landing
│       ├── browse.tsx                 # Browse corpus
│       ├── theorem.$id.tsx            # Theorem detail
│       ├── leaderboard.tsx            # Contributors
│       ├── api-docs.tsx               # API docs (was API.html)
│       ├── api-keys.tsx               # User's API keys (auth-gated)
│       ├── pricing.tsx
│       ├── signin.tsx                 # was Sign in.html (signin + signup tabs)
│       └── profile.tsx                # was Profile.html (auth-gated)
└── README.md
```

### 3.3 Routing decisions

- File-based routing via `@tanstack/router-plugin`. The router plugin emits `routeTree.gen.ts` automatically.
- All routes are SSR by default. The landing page and browse/theorem detail benefit from SSR for SEO; auth-gated routes (`/profile`, `/api-keys`) still SSR (showing the signed-in shell) but the data loaders short-circuit to a 401 redirect when `me()` returns 401.
- Redirects: the legacy filenames in `__root.tsx` are not preserved — links from the design HTMLs (`href="Browse.html"`, `href="Sign in.html"`, etc.) are rewritten to the new paths in the migrated components. Per-page mapping:

| Source HTML | Route path | Auth required |
|-------------|-----------|---------------|
| `Nasrudin Landing.html` | `/` | no |
| `Browse.html` | `/browse` | no |
| `Theorem.html` | `/theorem/$id` (default `9f3a2c8e` for direct visits) | no |
| `Leaderboard.html` | `/leaderboard` | no |
| `API.html` | `/api-docs` | no |
| `Pricing.html` | `/pricing` | no |
| `Sign in.html` | `/signin` | no |
| `Profile.html` | `/profile` | yes |
| (new) | `/api-keys` | yes |

`Profile.html`'s "API keys" affordance currently directs at `Profile.html` itself; we factor that out into `/api-keys` as a top-nav-linked page (the design's API.html already says "Generate keys from your profile" — we honour that intent by adding a link from `/profile` to `/api-keys` and surfacing the list on `/profile` too).

### 3.4 Data layer

`src/lib/api.ts`:

```ts
export const API_BASE = import.meta.env.VITE_API_URL ?? 'http://localhost:3001';

export class ApiError extends Error {
  constructor(public status: number, public body: unknown) { super(`API ${status}`); }
}

export async function apiFetch<T>(path: string, init?: RequestInit): Promise<T> {
  const res = await fetch(`${API_BASE}${path}`, {
    credentials: 'include',
    headers: { 'Content-Type': 'application/json', ...init?.headers },
    ...init,
  });
  if (!res.ok) throw new ApiError(res.status, await res.json().catch(() => null));
  return res.json() as Promise<T>;
}
```

`src/lib/queries.ts` exposes typed TanStack Query hooks: `useMe()`, `useTheorems(params)`, `useTheorem(id)`, `useLineage(id)`, `useDomains()`, `useApiKeys()`, `useCreateApiKey()`, `useRevokeApiKey()`, `useSavedSearches()`, `useWorkers()`, `useStats()`, `useDiscoveryStream()` (SSE wrapper).

Server-side route loaders use the **same** `apiFetch` (TanStack Start runs the loader on the server during SSR with the request cookies forwarded; no special `createServerFn` indirection). The single backend rule means we never call into Postgres or SeaORM from the frontend tree.

### 3.5 SSE on the landing page hero ticker

`hero.jsx`'s ticker hard-codes `TICKER_LINES`. We replace it with a live subscription to the existing `GET /api/events/discoveries` SSE endpoint, falling back to the static lines if the EventSource errors three times in a row. `WorkerMap` similarly reads `/api/workers` (poll every 30 s) for live worker pins; the static lat/long `WORKER_PINS` becomes a city-coordinate lookup table indexed by worker location.

### 3.6 Mock-data strategy

The JSX prototypes are full of inline JSX (`<>|⟨x,y⟩|<sup>2</sup>…</>`) for math statements. Real theorems from the API arrive as either Lean source or LaTeX strings. The plan:

- New helper `<TheoremStatement source={...} format="latex" | "lean" | "plain" />` that renders KaTeX for LaTeX strings and a syntax-highlit `<pre>` for Lean. The migrated landing components stop using inline JSX statements and instead render statements out of the API model.
- For the hero "live theorem" rotator on `/`, we fetch the three most recent verified theorems (`GET /api/theorems/recent?limit=3&verified=true`) and rotate through them.
- For the `FEATURED_REDISCOVERIES` block on the landing page, we ship a static curated list (`src/lib/featured.ts`) — those tiles include forward-looking aspirational entries (Schrödinger, Einstein field equations) that will never naturally appear in `/api/theorems/recent`. This is curation, not mock data.

## 4. Backend extension: `engine/crates/api` and `engine/crates/pg`

### 4.1 New entity: `api_keys`

`engine/crates/pg/src/entity/api_keys.rs`:

```rust
#[sea_orm(table_name = "api_keys")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,                       // surrogate id
    pub user_id: Option<Uuid>,          // FK users(id) ON DELETE CASCADE — NULL for worker keys
    pub kind: String,                   // "live" | "worker" (text, validated in handlers)
    pub name: String,                   // user-supplied label or worker handle
    pub prefix: String,                 // first 12 chars, e.g. "nsk_live_a98c"
    pub key_hash: String,               // Argon2 hash of the full key
    pub last_used_at: Option<DateTimeWithTimeZone>,
    pub expires_at: Option<DateTimeWithTimeZone>,
    pub created_at: DateTimeWithTimeZone,
    pub revoked_at: Option<DateTimeWithTimeZone>,
}
```

Indexes: `(user_id)`, `(kind)`, `UNIQUE (prefix)`, `UNIQUE (key_hash)`.

Migration: a new `m20260428_000002_api_keys.rs` appended to the `Migrator` list. The original `m20250101_000001_create_tables.rs` is left untouched — adding (not editing) the migration history is what SeaORM expects.

Query helpers (`engine/crates/pg/src/query/api_keys.rs`):

- `create(db, user_id, name, prefix, key_hash, expires_at) -> Model`
- `list_by_user(db, user_id) -> Vec<Model>` (excludes revoked)
- `find_by_prefix(db, prefix) -> Option<Model>` — used by the bearer auth path
- `mark_used(db, id, now)` — sets `last_used_at`
- `revoke(db, id, user_id) -> Option<Model>` — sets `revoked_at`
- `delete_expired(db, now) -> u64` — housekeeping

### 4.2 New extractor: `AuthOrApiKey`

`engine/crates/api/src/auth.rs` gains:

```rust
pub struct AuthOrApiKey(pub AuthUser);

impl<S: Send + Sync> FromRequestParts<S> for AuthOrApiKey {
    type Rejection = (StatusCode, Json<serde_json::Value>);
    async fn from_request_parts(parts: &mut Parts, state: &S) -> Result<Self, Self::Rejection> {
        // 1. Try the cookie session via AuthSession::from_request_parts.
        // 2. If absent, try `Authorization: Bearer nsk_<prefix>_<secret>`:
        //    - Split prefix/secret, look up by prefix, Argon2-verify secret against key_hash.
        //    - On match: load the user, mark_used asynchronously, return AuthOrApiKey(user).
        // 3. Otherwise: 401.
    }
}
```

Key format: `nsk_<kind>_<base32-secret>` where `<kind>` is `live` (user-issued, programmatic) or `worker` (machine-issued via `POST /api/workers/register`). No `test` keys in v1. The first 12 chars of the full key are stored as `prefix` (cleartext) and used to look up the row before the Argon2 verify; the full secret is never stored. The user only sees the full key at creation time.

This extractor replaces `AuthSess` on the platform handlers (api-keys, saved-searches, preferences, me/stats). The pre-existing `auth::{login,register,logout,me}` handlers keep using `AuthSess` because they need to *create* sessions, not consume them.

### 4.3 New handlers

All under `engine/crates/api/src/`:

| Module | Routes | Auth |
|--------|--------|------|
| `api_keys.rs` | `POST /api/api-keys` (create) <br> `GET /api/api-keys` (list) <br> `DELETE /api/api-keys/{id}` (revoke) | `AuthSess` (cookie only — keys can't create keys) |
| `saved_searches.rs` | `POST /api/saved-searches` <br> `GET /api/saved-searches` <br> `DELETE /api/saved-searches/{id}` <br> `PATCH /api/saved-searches/{id}` | `AuthOrApiKey` |
| `preferences.rs` | `GET /api/preferences` <br> `PATCH /api/preferences` | `AuthOrApiKey` |
| `workers.rs` | `POST /api/workers/register` (open + worker key — see §4.4) <br> `POST /api/workers/heartbeat` (worker key) <br> `GET /api/workers` (open) <br> `GET /api/workers/me` (worker key) | mixed |
| `me.rs` | `GET /api/me/stats` (saved-count, api-call-count, etc.) | `AuthOrApiKey` |

`api_keys::create` returns `{ id, prefix, full_key, created_at, expires_at, name }` — `full_key` is the **only** time the secret is in the response body. List/revoke return only metadata (no `full_key`).

### 4.4 Worker authentication

Worker registration is a different beast from user API keys: a worker is unattended, registers itself, and heartbeats. The simplest design that fits the existing schema:

- `POST /api/workers/register` is unauthenticated. It creates a row in `workers`, creates a paired row in `api_keys` with `kind=worker` (i.e. prefix `nsk_worker_…`) and `user_id = NULL` (workers are not users), and returns `{ worker_id, api_key }`. The worker stores both locally. The api-key row's `name` is set to the worker handle for human-readable bookkeeping.
- Migration tweak: `api_keys.user_id` is **nullable** so worker keys can exist without a user owner. List/revoke for user keys filters `WHERE user_id = $current_user`, which naturally excludes worker keys.
- `POST /api/workers/heartbeat` requires the worker key as `Authorization: Bearer nsk_worker_…` and updates `workers.last_seen` + `workers.theorems_contributed`. The bearer extractor's "user lookup" step short-circuits on `kind=worker` and instead returns a `WorkerCredential` (a separate extractor type, `WorkerAuth`, that never resolves to `AuthUser`).
- `AuthOrApiKey` rejects worker keys with 401: a worker should not be able to call `/api/preferences`. This separation keeps the user surface and the worker surface from cross-pollinating.

This keeps a single credential model. If we need to revoke worker access in the future, revoking the api-key row severs both heartbeats and any other API call.

### 4.5 Rate-limit groups

The existing four governor groups (`api_standard`, `health_relaxed`, `auth_strict`, `auth_session`) cover the core surface. New groups:

- `platform_user` (60 req/min, burst 30) — for `api-keys`, `saved-searches`, `preferences`, `me/stats`. Keyed by IP for cookie sessions and by api-key prefix for bearer requests.
- `platform_worker` (300 req/min, burst 120) — for `workers/heartbeat`. Workers heartbeat once a minute by default; this is generous to allow batches.

The existing `api_standard` group covers the public theorem reads.

### 4.6 CORS

`engine/crates/api/src/main.rs` already restricts CORS to `http://localhost:3000`. The Bearer flow does not depend on CORS, but we add `Authorization` to the allowed headers (it's already in the list) and ensure `expose_headers` includes `X-RateLimit-Remaining` if we surface rate-limit headers later. No further CORS changes for v1.

### 4.7 New `migrate` binary

`just db-migrate` calls `cargo run --bin migrate`. There is no such bin today (the api server runs migrations on startup). We add `engine/crates/pg/src/bin/migrate.rs`:

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    dotenvy::dotenv().ok();
    let url = std::env::var("DATABASE_URL")?;
    let db = nasrudin_pg::connect_simple(&url).await?;
    nasrudin_pg::run_migrations(&db).await?;
    println!("migrations complete");
    Ok(())
}
```

This unblocks the existing `just db-migrate` recipe and lets us run migrations independently of starting the server.

## 5. Auth + session flow

1. **Sign up.** `/signin` shows tabs (signin / signup). Submit POST to `/api/auth/register`. Response sets the session cookie and returns the user. Frontend invalidates the `me` query and navigates to `/profile`.
2. **Sign in.** Same form, posts to `/api/auth/login`. Same redirect.
3. **Session check.** Every page mounts a `useMe()` query; auth-gated routes use `useMe`'s data in their `beforeLoad` to redirect to `/signin` on 401.
4. **Sign out.** `POST /api/auth/logout`, invalidate `me`, navigate to `/`.
5. **API key creation.** From `/api-keys`: name → `POST /api/api-keys` with cookie auth → response shows the full key in a **modal that requires the user to confirm they've copied it** (single-shot reveal). Revoke is a row-level button.
6. **Bearer use.** External clients send `Authorization: Bearer nsk_live_<secret>`. The extractor verifies, marks used, attaches the user.

OAuth providers (ORCID/GitHub/Google/SSO) shown in the design are **out of scope for v1**. The OAuth buttons in the migrated `AuthForm` are rendered as disabled with a "coming soon" tooltip.

## 6. Error handling

- **Frontend.** A root error boundary in `__root.tsx` renders a paper-textured error card. Per-route `errorComponent` for resource-specific errors. 404 page rendered via the router's `notFoundComponent`.
- **Network.** `apiFetch` throws `ApiError`; TanStack Query retries on idempotent reads (default 3 retries, exponential). Mutations surface errors directly to the form (no auto-retry).
- **Auth boundary.** A 401 response from any query triggers a one-time refetch of `useMe`; if `me` itself returns 401 we navigate to `/signin?redirect=<current>`.
- **Backend.** Handlers return `Json<serde_json::Value>` with `{ "error": "<msg>" }` and the right `StatusCode` (matches the existing convention in `main.rs`). The api-key creation handler returns 409 on duplicate name.
- **Bearer rejection.** Malformed bearer or revoked key returns 401 with `{ "error": "invalid api key" }`. Expired key returns 401 with `{ "error": "expired api key" }`.

## 7. Testing

### 7.1 Backend (Rust)

- `engine/crates/pg/tests/api_keys.rs` (new) — round-trip: create → list → mark_used → revoke. Uses `sqlx::testing` against the docker-compose Postgres (skipped if `DATABASE_URL` unset).
- `engine/crates/api/tests/auth_or_apikey.rs` (new) — spawns the router with an in-memory store, asserts cookie session and bearer-key paths both authorize the same handler. Asserts revoked key → 401.
- `engine/crates/api/tests/platform_endpoints.rs` (new) — smoke test for each new handler against a real db.

### 7.2 Frontend (TypeScript)

- `vitest` smoke test that the route tree compiles and `__root` renders without error using `@tanstack/react-router`'s test utilities.
- A single `apiFetch` test that verifies `credentials: 'include'` and error mapping.
- We do **not** introduce Playwright in v1. Manual run-through with `pnpm dev` against a running api server is the v1 acceptance check.

### 7.3 Lint / type / format gates

- `pnpm check` runs `biome check . && tsc --noEmit`.
- `pnpm format` runs `biome format --write .`.
- Existing `just check` keeps working (it already calls `pnpm check` and `cargo clippy`).

## 8. Out of scope (v1)

- OAuth (ORCID/GitHub/Google/SSO).
- Billing / Stripe / actual paid tier enforcement. The pricing page and tier cards render but the CTAs are placeholders.
- Per-key scopes (read-only vs write). All keys grant the same access as the owning user.
- Rate-limit headers in responses.
- Real "targeted search" submission flow (the form posts to a `/api/searches/targeted` stub that returns 501 Not Implemented).
- Re-verify in browser. The button on `/theorem/$id` runs the fake animation from the prototype; backing it with real Lean is a future phase.
- Removing the `tweaks-panel.jsx` design tool — we do not migrate it. Production builds do not include a tweaks panel.

## 9. File-level change list

### 9.1 New files

```
nasrudin-frontend/                        (entirely new tree, listed above)
engine/crates/pg/src/entity/api_keys.rs
engine/crates/pg/src/query/api_keys.rs
engine/crates/pg/src/migrator/m20260428_000002_api_keys.rs
engine/crates/pg/src/bin/migrate.rs
engine/crates/api/src/handlers/api_keys.rs
engine/crates/api/src/handlers/saved_searches.rs
engine/crates/api/src/handlers/preferences.rs
engine/crates/api/src/handlers/workers.rs
engine/crates/api/src/handlers/me.rs
engine/crates/pg/tests/api_keys.rs
engine/crates/api/tests/auth_or_apikey.rs
engine/crates/api/tests/platform_endpoints.rs
docs/superpowers/specs/2026-04-28-frontend-rebuild-tanstack-start-design.md  (this file)
```

### 9.2 Files modified

```
engine/crates/pg/src/entity/mod.rs                     (add api_keys)
engine/crates/pg/src/query/mod.rs                      (add api_keys)
engine/crates/pg/src/migrator/mod.rs                   (register new migration)
engine/crates/pg/src/lib.rs                            (re-export api_keys types)
engine/crates/pg/Cargo.toml                            (add password-auth, base32)
engine/crates/api/src/auth.rs                          (add AuthOrApiKey extractor)
engine/crates/api/src/main.rs                          (mount new handlers + groups)
engine/crates/api/src/rate_limit.rs                    (add platform_user, platform_worker)
engine/crates/api/Cargo.toml                           (add base32 if needed)
docker-compose.yml                                     (already modified by user — leave)
.env.example                                           (no changes; FE uses VITE_API_URL only)
justfile                                               (no changes; existing recipes already match)
README.md                                              (add /api-keys to the "platform features" list)
pnpm-workspace.yaml                                    (no changes)
```

### 9.3 Files deleted

The eight prototype HTML files, the five JSX files, and the three CSS files in `nasrudin-frontend/` (root level, not `assets/`). The CSS files are *moved* to `nasrudin-frontend/src/styles/` rather than deleted; `assets/pattern-geometric.svg` moves to `public/`.

## 10. Risks and decisions to revisit

- **TanStack Start v1 stability.** TanStack Start went stable on v1 in late 2025 / early 2026. If a version pinned by `latest` ends up broken at install time, fall back to the most recent prior tag and pin in `package.json`. We do not chase a beta or a release candidate.
- **SSR + cookies + CORS.** TanStack Start's loader runs server-side; when SSRing an authenticated page, the loader needs the request cookies forwarded to `:3001`. We use TanStack Start's request context to pull `cookie` off the incoming request and inject it into `apiFetch` for SSR runs. Implementation lands in `src/lib/api.ts` behind an `import.meta.env.SSR` branch.
- **`window.NASRUDIN_DATA` global.** The prototype JSX wires components to a global. The migration replaces that global with explicit React props or TanStack Query data. No global state survives.
- **KaTeX bundle size.** ~270 KB. Acceptable for a math-first product. We code-split it from the landing route if it pushes total landing JS above 1 MB.
- **`pnpm-lock.yaml` churn.** The `latest` rule means the lockfile changes every time we `pnpm install`. The implementation plan locks an explicit version per dep and commits the lock in one go.

## 11. Open questions

None at design time. Implementation may surface specific package-version pins; those are decisions for the implementation plan, not the design.
