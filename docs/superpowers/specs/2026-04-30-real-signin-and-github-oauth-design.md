# Design: Real Sign-In Page (Live Stats + GitHub OAuth)

**Date:** 2026-04-30
**Status:** Approved
**Scope:** Replace hardcoded marketing stats on `/signin` with live data, and wire up the first real OAuth provider (GitHub) on the existing `axum-login` backend.

---

## Background

The sign-in page (`nasrudin-frontend/src/routes/signin.tsx`) presents two surfaces that look unfinished:

1. The sidebar shows three hardcoded stats: `247,118 Verified theorems`, `1,247 Workers · live`, `42 Countries`. They are literal JSX values, not API-driven.
2. The auth form (`nasrudin-frontend/src/components/auth/AuthForm.tsx`) renders four OAuth buttons (`ORCID`, `GitHub`, `Google`, `Institution SSO`) all `disabled` with a `"Coming soon"` tooltip.

The email/password path is **not** fake — it is wired to a real backend (`POST /api/auth/{login,register,logout}`, `GET /api/auth/me`) implemented with `axum-login` + PostgreSQL (SeaORM) + Argon2 hashing in `engine/crates/api/src/auth.rs`. That backend is also the source of identity for Stripe billing, API keys (`nsk_live_*`), worker keys (`nsk_worker_*`), saved searches, LLM keys, and worker reputation. **Migrating to a managed provider (Clerk, Auth0) was rejected** because it would force re-architecting all of those systems against a foreign user-ID space; the cost vastly exceeds the benefit for a working homegrown auth.

The actual gap is OAuth. We address it by adding GitHub as the first real provider, and removing the placeholder buttons for the others until they are genuinely implemented.

## Goals

- The `/signin` sidebar stats reflect real database values, refreshed at most every 60 seconds.
- A user can complete the full GitHub OAuth flow and land authenticated on `/profile`.
- The sign-in page no longer shows disabled "Coming soon" buttons.

## Non-Goals

- Google, ORCID, or Institution SSO providers.
- Account-linking UI (a user-facing screen for connecting/disconnecting OAuth identities). Auto-link by verified email is the policy; an explicit UI is deferred.
- Password reset, email verification, or MFA.
- Unlinking GitHub from an account.

---

## Component 1 — Landing Stats Endpoint

### Endpoint
`GET /api/stats/landing` → `200 application/json`

```json
{
  "verified_theorems": 247118,
  "active_workers": 1247,
  "contributors": 308
}
```

### Sources
- `verified_theorems` — count from RocksDB stats already exposed by the `rocks` crate. Use the existing stats accessor; do not scan column families.
- `active_workers` — `SELECT count(*) FROM workers WHERE last_heartbeat > now() - interval '5 minutes'`. Add a query helper in `engine/crates/pg/src/query/workers.rs` if one doesn't already exist with this exact predicate.
- `contributors` — `SELECT count(distinct user_id) FROM workers WHERE user_id IS NOT NULL`. (Could also count `users` rows; `workers.user_id` was chosen because it represents people who actually contributed compute, which is the more meaningful number on a sign-in landing.)

The `"42 Countries"` stat is **dropped**: we do not record geography. The sidebar renders **three** stats: verified theorems, active workers, contributors.

### Caching
In-process cache in API state. No new dependency:

```rust
struct LandingStatsCache {
    inner: tokio::sync::RwLock<Option<(std::time::Instant, LandingStats)>>,
}
```

If the cached value is younger than 60 seconds, return it; otherwise recompute under the write lock and update. Single in-flight recomputation is acceptable; we do not need request coalescing at this scale.

### Auth
Public (no auth required). The endpoint is rate-limited only by the global axum middleware already in place.

### Frontend
- Add `useLandingStats()` to `nasrudin-frontend/src/lib/queries.ts` using TanStack Query. `staleTime: 60_000`, `refetchOnWindowFocus: false`.
- `signin.tsx` consumes the hook. While loading, render `—` placeholders in the same `.num` slot to avoid layout shift. On error, fall back to `—` (do not break the page).

---

## Component 2 — GitHub OAuth

### Backend module
New file: `engine/crates/api/src/auth_oauth.rs`. Routes registered in the existing router under `/api/auth/`:

- `GET /api/auth/github/start`
  - Generate 32-byte random `state`, base64url-encode.
  - Store `state` in a short-lived (5 min) signed cookie (`github_oauth_state`, `HttpOnly`, `SameSite=Lax`, `Secure` in prod).
  - 302 redirect to `https://github.com/login/oauth/authorize?client_id=…&redirect_uri=…&scope=read:user%20user:email&state=…`.

- `GET /api/auth/github/callback?code=…&state=…`
  - Read `github_oauth_state` cookie, verify equality with query param. If absent or mismatched → 400.
  - Clear the state cookie.
  - Exchange `code` for access token via `oauth2` crate against `https://github.com/login/oauth/access_token`.
  - Fetch `GET https://api.github.com/user` (id, login, name, avatar_url) and `GET https://api.github.com/user/emails` (find the primary verified email).
  - Apply find-or-create logic (below).
  - `auth_session.login(&user).await` — reuses existing axum-login session machinery.
  - 302 redirect to `/profile`. (Include `?welcome=1` if newly created — frontend may show a one-time toast, optional.)

### Find-or-create logic
Implemented in `engine/crates/pg/src/query/users.rs` as `find_or_create_from_github(db, github_id, github_login, email, display_name)`:

1. **Match by `github_id`** — if a row has this `github_id`, return it. Update `github_login` and `display_name` if changed.
2. **Match by email** — if a row has this email (case-insensitive, normalized) and `github_id IS NULL`, **link**: set `github_id` and `github_login` on that row, return it. Email must be the **primary verified** one from GitHub.
3. **Create** — insert new row with `password_hash = NULL`, `github_id`, `github_login`, `email`, `display_name`, `plan_tier = 'free'`.

The auto-link-by-email policy was explicitly approved. Rationale: GitHub guarantees the email is verified, so we are not at risk of a hostile actor claiming a stranger's account by registering a matching GitHub email — they would have to control the inbox already. This avoids a friction cliff for users who originally signed up with password and now click the GitHub button.

### Schema change
New migration: `engine/crates/pg/src/migrator/m20260430_000014_user_oauth_identity.rs`.

```sql
ALTER TABLE users ADD COLUMN github_id BIGINT NULL UNIQUE;
ALTER TABLE users ADD COLUMN github_login TEXT NULL;
ALTER TABLE users ALTER COLUMN password_hash DROP NOT NULL;
```

Existing rows have a `password_hash`, so dropping `NOT NULL` is non-breaking. `github_id` is `UNIQUE NULL` — Postgres allows multiple `NULL`s in a unique index, which is what we want.

Update `engine/crates/pg/src/entity/users.rs` SeaORM entity: add `github_id: Option<i64>`, `github_login: Option<String>`, change `password_hash: String` → `password_hash: Option<String>`.

The `AuthUser` wrapper in `engine/crates/api/src/auth.rs` and `axum_login::AuthUser::session_auth_hash()` currently returns `password_hash.as_bytes()`. For OAuth-only users `password_hash` is `None`; return the `github_id`'s big-endian bytes as the session auth hash in that case (any stable per-user secret works for axum-login's invalidate-on-password-change check).

### Config
New env vars consumed in `engine/crates/api/src/state.rs`:

- `GITHUB_OAUTH_CLIENT_ID`
- `GITHUB_OAUTH_CLIENT_SECRET`
- `GITHUB_OAUTH_REDIRECT_URI` (e.g., `https://nasrudin.app/api/auth/github/callback` in prod, `http://localhost:8080/api/auth/github/callback` in dev)

If any are unset, `/api/auth/github/start` and `/callback` return `503 { "error": "oauth_not_configured" }`. Server startup is **not** affected. This lets developers run the full stack without GitHub credentials.

`.env.example` updated. A short paragraph in `deploy/README.md` (or wherever deployment is documented) explains how to register the GitHub OAuth app and where to put the values.

### Frontend
`nasrudin-frontend/src/components/auth/AuthForm.tsx`:

- Replace the OAuth grid with a **single full-width "Continue with GitHub"** button rendered **above** the email form, then a horizontal `or` divider, then the existing email/password form.
- The button is a real `<a href="/api/auth/github/start" class="btn btn-secondary">` (anchor, not button — it's a navigation, not a form submit). It uses the GitHub `<svg>` mark to the left of the label.
- Remove the `oauth-grid`, the four disabled buttons, and the `divider` element ("Or continue with"). Add a single `divider` ("or") between the GitHub button and the email form.

`nasrudin-frontend/src/routes/signin.tsx`:

- Replace the three hardcoded `.auth-stat` blocks with values from `useLandingStats()`.
- If `useLandingStats()` is loading or errored, render `—` for the number while keeping the label.

---

## Component 3 — No-op for logout / nav

`useLogout` and the rest of the session machinery already work. No changes.

---

## Testing

### Unit tests (Rust)
- `query::users::find_or_create_from_github`:
  - branch 1: existing row with same `github_id` → returns existing, updates `display_name` if changed.
  - branch 2: existing row with same email, `github_id IS NULL` → links and returns.
  - branch 3: no match → creates new row with `password_hash = NULL`.

### Integration tests (Rust, against test DB)
- `GET /api/stats/landing` returns the expected shape and types.
- Same endpoint hit twice within 60s returns identical bytes (cache hit).

### Manual test (one-time)
- Register a GitHub OAuth app pointing at `http://localhost:8080/api/auth/github/callback`.
- Walk through `/signin` → "Continue with GitHub" → GitHub authorize → land on `/profile` authenticated.
- Walk through the email-collision path: register `x@example.com` with password, log out, sign in with a GitHub account whose primary verified email is `x@example.com`, verify the same `users.id` is reused.

We deliberately do **not** mock GitHub's OAuth endpoints in an automated test; the integration cost exceeds the value at this stage.

---

## Migration & rollout

1. Ship migration `m20260430_000014_user_oauth_identity` first (additive, safe to deploy without code changes).
2. Ship API + frontend together. If GitHub credentials are not yet configured in the prod env, the GitHub button returns 503 — surface this as a small inline error on `/signin` rather than a hard failure (the email form still works).
3. Configure `GITHUB_OAUTH_*` env vars in prod once the GitHub OAuth app is registered.

No data backfill required. No breaking change to existing API contracts.

---

## Risks

- **Email-impersonation via OAuth provider** — mitigated by requiring `primary == true && verified == true` on the GitHub email object. We do not link on unverified emails.
- **Session hash invalidation** — for OAuth-only users, returning `github_id` bytes from `session_auth_hash` means rotating `github_id` (which we never do) would invalidate sessions. Acceptable.
- **`password_hash NOT NULL` drop** — reversible only with a backfill if we ever wanted to re-tighten. We accept that; the column is genuinely optional now.
- **Cache staleness on stats** — 60s of staleness on a marketing stat is invisible to users. Acceptable.

---

## Files touched (estimate)

**Backend (Rust)**
- `engine/crates/api/src/auth_oauth.rs` (new, ~200 lines)
- `engine/crates/api/src/handlers/stats.rs` (new or extend existing, ~80 lines)
- `engine/crates/api/src/state.rs` (add OAuth config + stats cache)
- `engine/crates/api/src/main.rs` or router file (register routes)
- `engine/crates/api/src/auth.rs` (handle `Option<String>` password_hash in `AuthUser`)
- `engine/crates/api/Cargo.toml` (add `oauth2` dep)
- `engine/crates/pg/src/migrator/m20260430_000014_user_oauth_identity.rs` (new)
- `engine/crates/pg/src/migrator/mod.rs` (register migration)
- `engine/crates/pg/src/entity/users.rs` (new fields, nullable password_hash)
- `engine/crates/pg/src/query/users.rs` (`find_or_create_from_github`)
- `engine/crates/pg/src/query/workers.rs` (active count, distinct user count)

**Frontend (TS)**
- `nasrudin-frontend/src/lib/queries.ts` (`useLandingStats`)
- `nasrudin-frontend/src/components/auth/AuthForm.tsx` (rewrite OAuth section)
- `nasrudin-frontend/src/routes/signin.tsx` (consume `useLandingStats`)

**Config / docs**
- `.env.example`
- `deploy/README.md` (or equivalent) — short note on GitHub OAuth app registration
