# Design: Firebase Auth Migration

**Date:** 2026-04-30
**Status:** Approved
**Scope:** Replace the email/password + GitHub OAuth login flow (axum-login + Argon2) with Firebase Authentication. Day-1 providers are email/password (with Firebase's built-in email verification + password reset) and Google OAuth. All existing GitHub OAuth scaffolding and the email/password handlers shipped in the previous round are deleted as part of this migration.

---

## Background

The previous spec (`2026-04-30-real-signin-and-github-oauth-design.md`) added GitHub OAuth on top of axum-login + Argon2. While that flow works, the underlying axum-login backend has fundamental feature gaps: **no password reset, no email verification, no MFA, no SMS OTP**. Building any of these in-house is several days of careful work plus ongoing operational burden (SMTP deliverability, Twilio account, TOTP enrollment UI, recovery codes).

Firebase Authentication ships all of these out of the box, scales free up to 50,000 monthly active users, and integrates cleanly with our axum-login session machinery via short-lived ID tokens. The user has zero accounts in production today, so we can do a clean break — drop the password and GitHub columns, drop the in-house auth handlers, and route all sign-in through Firebase.

The user table itself stays. `users.id` (UUID) remains the foreign key on `api_keys`, `workers`, `saved_searches`, `user_preferences`, `user_llm_keys`, `library_folders`, `user_saved_theorems`, plus the Stripe customer linkage. We add `firebase_uid TEXT NOT NULL UNIQUE` as the lookup key from Firebase identities to our users.

Worker authentication (`nsk_worker_*` bearer tokens) and live API-key authentication (`nsk_live_*`) are unaffected — they don't go through Firebase.

## Goals

- A user can sign up with email + password, verify their email via a Firebase-sent link, and sign in.
- A user can sign in with Google.
- A user can reset a forgotten password via a Firebase-sent reset link.
- The backend continues to expose `GET /api/auth/me` and `POST /api/auth/logout` against axum-login sessions; no handler outside the auth module changes.
- Existing API key and worker key flows continue to work without modification.

## Non-Goals

- TOTP MFA, SMS OTP, Apple sign-in, GitHub-via-Firebase — each deferred to a follow-up spec.
- Account-linking UI. Firebase auto-links providers by email; no in-app screen needed Day 1.
- Custom Firebase claims. `plan_tier` and other per-user metadata stay in our DB.
- Migration of existing users. There are none.

---

## Architecture

The split:

- **Firebase owns:** signup, login, password storage, password reset, email verification, the Google OAuth flow.
- **Our backend owns:** the `users` table (UUID primary key), Stripe linkage, API keys, plan tiers, all foreign keys, and axum-login sessions.
- **The bridge:** a single new endpoint, `POST /api/auth/firebase-session`. The frontend obtains a Firebase ID token (signed JWT) from the Web SDK, posts it once, and receives an axum-login session cookie. All subsequent requests use the cookie. The Firebase ID token is not used per-request.

This keeps the existing `AuthSess` and `AuthOrApiKey` extractors and every handler that consumes them untouched.

---

## Component 1 — Schema Migration

New migration: `engine/crates/pg/src/migrator/m20260430_000016_firebase_auth.rs`.

```sql
-- Wipe — there are no production accounts; cascade clears every dependent row.
DELETE FROM users;

-- Drop columns no longer needed.
ALTER TABLE users DROP COLUMN password_hash;
ALTER TABLE users DROP COLUMN github_id;
ALTER TABLE users DROP COLUMN github_login;

-- Add the Firebase identity link.
ALTER TABLE users ADD COLUMN firebase_uid TEXT NOT NULL UNIQUE;
```

Migration `m20260430_000014_user_oauth_identity` stays in history (it shipped). This new migration effectively reverts and replaces it with a Firebase-shaped schema.

The `down` migration restores `password_hash`, `github_id`, `github_login`, and drops `firebase_uid`. We do not attempt to back-fill any data.

Update `engine/crates/pg/src/entity/users.rs`: drop `password_hash`, `github_id`, `github_login` fields; add `firebase_uid: String`.

---

## Component 2 — Backend ID Token Verification

New module: `engine/crates/api/src/firebase_auth.rs`.

### Public surface

```rust
pub struct FirebaseClaims {
    pub uid: String,           // JWT `sub`
    pub email: String,
    pub email_verified: bool,
    pub name: Option<String>,
    pub picture: Option<String>,
    pub sign_in_provider: String,  // e.g. "password", "google.com"
}

pub async fn verify_id_token(
    token: &str,
    project_id: &str,
    jwks: &JwksCache,
) -> Result<FirebaseClaims, VerifyError>;
```

### Implementation

- **JWKs cache.** Fetches `https://www.googleapis.com/robot/v1/metadata/x509/securetoken@system.gserviceaccount.com` on first use; refreshes whenever a token's `kid` is not in cache; refreshes preemptively every hour. Stored as `Arc<RwLock<HashMap<String, DecodingKey>>>` on `AppState`.
- **Verification steps:**
  1. Decode JWT header → extract `kid`. If missing → reject.
  2. Look up `kid` in cache. On miss → refresh JWKs once, retry. On second miss → reject.
  3. Verify RS256 signature with `jsonwebtoken` crate.
  4. Verify standard claims:
     - `iss == https://securetoken.google.com/{project_id}`
     - `aud == {project_id}`
     - `exp > now` (with no leeway — the Web SDK auto-refreshes well before expiry)
     - `iat <= now + 60s` (small leeway for clock skew)
     - `sub` non-empty
  5. Return `FirebaseClaims`.
- **Errors:** `VerifyError` enum with `Expired`, `WrongIssuer`, `WrongAudience`, `BadSignature`, `MalformedToken`, `JwksFetch(reqwest::Error)`. All map to 401 in the handler except `JwksFetch` which maps to 502.

### Configuration

- New env var: `FIREBASE_PROJECT_ID` (a string like `nasrudin-prod`). Required for the `/api/auth/firebase-session` endpoint to function — without it the route returns 503.
- No service-account JSON / Admin SDK credentials are needed. ID-token verification is fully offline once JWKs are fetched.

### Dependencies

- `jsonwebtoken = "9"` — well-maintained, used widely.
- `reqwest` — already a workspace dep, used for fetching JWKs.

---

## Component 3 — Session Endpoint

`POST /api/auth/firebase-session`

Located in `engine/crates/api/src/auth.rs` (replacing the deleted `register` and `login` handlers).

### Request

```json
{ "id_token": "eyJhbGciOiJSUzI1NiIs..." }
```

### Behavior

1. If `state.firebase_project_id.is_none()` → 503 `oauth_not_configured`.
2. Verify the token via `firebase_auth::verify_id_token`. On failure → 401 with the appropriate error code.
3. **Strict email verification:** if `claims.email_verified == false` AND `claims.sign_in_provider == "password"` → 403 `email_not_verified`. (Google-issued emails are pre-verified by Google, so they pass through.)
4. Find or create user in `users`:
   - Match on `firebase_uid == claims.uid` → return existing row.
   - Else: insert new row. `firebase_uid = claims.uid`, `email = claims.email`, `display_name = claims.name`, `plan_tier = 'free'`, all Stripe / billing columns `NULL`, `research_credits = 0`.
5. Issue session: `auth_session.login(&AuthUser::from_model(user)).await`.
6. Response: `200 application/json` with the `AuthUser` body — same shape returned by `GET /api/auth/me`.

### Rate limit

Shares the existing `auth_strict` bucket (5 req/min, burst 5, per-IP). Same threat profile as `/login` had.

### Why not "find by email" before insert?

There are no existing rows. Future-proofing for email-based linking is unnecessary because Firebase does its own provider linking by email — when a user signs in with Google whose email matches an existing Firebase email/password account, Firebase merges them under one UID. We never see two Firebase UIDs for the same human.

---

## Component 4 — Code Deletion

**Backend deletions:**

- `engine/crates/api/src/auth_oauth.rs` — entire file.
- `engine/crates/api/src/auth.rs::register` and `login` handlers.
- Routes in `main.rs`: `/api/auth/register`, `/api/auth/login`, `/api/auth/github/start`, `/api/auth/github/callback`.
- `state::GithubOAuthConfig` struct and `AppState::oauth_github` field.
- Env loading for `GITHUB_OAUTH_CLIENT_ID`, `GITHUB_OAUTH_CLIENT_SECRET`, `GITHUB_OAUTH_REDIRECT_URI`, `OAUTH_COOKIE_SECURE` in `main.rs`.
- `nasrudin_pg::query::users::find_or_create_from_github` and its tests in `engine/crates/pg/tests/users_oauth_link.rs`.
- The `oauth2` dependency from `engine/crates/api/Cargo.toml`.

**Backend updates:**

- `auth::AuthUser`: drop `password_hash`, `github_id`, `github_login`, `auth_hash_bytes`. Add `firebase_uid: String`. `session_auth_hash` returns `firebase_uid.as_bytes()`.
- `auth::Backend::authenticate`: still required by `axum_login::AuthnBackend` trait but never called (no password to authenticate). Implement to return `Ok(None)` always.
- `nasrudin_pg::query::users::create_user`: replace with `create_firebase_user(db, firebase_uid, email, display_name)` that takes the four required fields. The old signature with `Option<&str>` password hash goes away.

**Backend retained (unchanged):**

- `/api/auth/logout` and `/api/auth/me` handlers.
- `AuthSess`, `AuthOrApiKey`, `WorkerAuth` extractors.
- `nasrudin_pg::query::users::{find_by_id, find_by_email, set_stripe_customer_id, update_display_name, delete_user, *_research_credits, grant_research_credits_on_period_advance}`.

**Frontend deletions:**

- The "Continue with GitHub" anchor in `AuthForm.tsx`.
- The `useLogin`, `useRegister` implementations that POST to `/api/auth/login` and `/api/auth/register` (replaced — see Component 5).

**Configuration deletions:**

- `.env.example`: remove the `# ── GitHub OAuth ──` block (`GITHUB_OAUTH_CLIENT_ID`, `GITHUB_OAUTH_CLIENT_SECRET`, `GITHUB_OAUTH_REDIRECT_URI`, `OAUTH_COOKIE_SECURE`).
- `deploy/README.md`: remove the GitHub OAuth section (replaced by the Firebase setup section in Component 7).

---

## Component 5 — Frontend Rewrite

### New dependency

`pnpm -C nasrudin-frontend add firebase`

### New env vars (frontend)

These are public per Firebase's documented threat model — safe to ship in the bundle:

```
VITE_FIREBASE_API_KEY
VITE_FIREBASE_AUTH_DOMAIN
VITE_FIREBASE_PROJECT_ID
VITE_FIREBASE_STORAGE_BUCKET
VITE_FIREBASE_MESSAGING_SENDER_ID
VITE_FIREBASE_APP_ID
```

### New file: `nasrudin-frontend/src/lib/firebase.ts`

Initializes Firebase. Exports:
- `auth` — the `Auth` instance.
- `signInWithEmail(email, password): Promise<UserCredential>`
- `signUpWithEmail(email, password): Promise<UserCredential>`
- `signInWithGoogle(): Promise<UserCredential>` — uses `signInWithPopup(GoogleAuthProvider)`.
- `sendPasswordReset(email): Promise<void>`
- `sendVerificationEmail(): Promise<void>` — sends to current user.
- `firebaseSignOut(): Promise<void>`
- `getCurrentIdToken(): Promise<string | null>` — returns fresh token, refreshing if near expiry.

### `AuthForm.tsx` rewrite

Layout (top to bottom):
1. Heading: "Welcome back." / "Join the corpus." (unchanged).
2. Lede paragraph (unchanged).
3. **Full-width "Continue with Google" button** — primary style, with the Google "G" SVG.
4. `or` divider.
5. Sign-in / Create account tabs.
6. Email + password fields (signup also shows display_name).
7. **"Forgot password?"** link below the password field on the sign-in tab. Click → inline reset flow: email field, "Send reset link" button, success state ("Check your inbox").
8. Submit button.
9. After signup: inline alert "Check your email to verify your address. [Resend verification email]". Frontend stores a flag in local React state; if user reloads, the flag is gone (acceptable — they'll see the alert again on the next sign-in attempt).
10. Terms / privacy line at bottom (unchanged).

### Hook rewrite in `lib/queries.ts`

```ts
export function useLogin() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async (creds: { email: string; password: string }) => {
      const cred = await signInWithEmail(creds.email, creds.password);
      const idToken = await cred.user.getIdToken();
      return apiFetch<AuthUser>('/api/auth/firebase-session', {
        method: 'POST',
        body: JSON.stringify({ id_token: idToken }),
      });
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}
```

Same shape for `useRegister` (calls `signUpWithEmail` then `sendVerificationEmail` then exchange) and `useGoogleLogin` (calls `signInWithGoogle` then exchange).

`useLogout` calls both `firebaseSignOut()` and `apiFetch('/api/auth/logout', { method: 'POST' })` so both client and server forget the user.

`useResetPassword(email)` is a single-shot mutation that calls `sendPasswordReset(email)`. Server is not involved.

`useResendVerification()` calls `sendVerificationEmail()`. Server is not involved.

`useMe()` is unchanged — still GETs `/api/auth/me`.

### Error handling

Firebase throws coded errors (`auth/invalid-credential`, `auth/wrong-password`, `auth/user-not-found`, `auth/too-many-requests`, etc.). The hook layer catches these and re-throws as `Error` with a human-readable message that the form renders inline. Reference table maintained in `lib/firebase.ts`.

The session-exchange endpoint can return 403 `email_not_verified` — the form catches this and renders the "verify your email" alert with the resend button.

---

## Component 6 — Configuration & Deploy Docs

### `.env.example`

Remove the GitHub OAuth block. Add:

```sh
# ── Firebase Auth ─────────────────────────────────────────
# Backend: only the project ID is needed to verify Firebase ID tokens.
# When unset, /api/auth/firebase-session returns 503 and the rest of the API works.
FIREBASE_PROJECT_ID=

# Frontend (VITE_*): these are public per Firebase's threat model.
# Get them from console.firebase.google.com → Project settings → Your apps → Web.
VITE_FIREBASE_API_KEY=
VITE_FIREBASE_AUTH_DOMAIN=
VITE_FIREBASE_PROJECT_ID=
VITE_FIREBASE_STORAGE_BUCKET=
VITE_FIREBASE_MESSAGING_SENDER_ID=
VITE_FIREBASE_APP_ID=
```

### `deploy/README.md`

Replace the GitHub OAuth section with a Firebase setup section:

> ## Firebase Auth (sign-in)
>
> Sign-in is powered by Firebase Authentication. To bring up a fresh environment:
>
> 1. Visit <https://console.firebase.google.com> → **Add project** → name it (e.g. `nasrudin-prod`, `nasrudin-staging`).
> 2. **Authentication → Get started** → enable:
>    - **Email/Password** (with the "Email verification" template enabled)
>    - **Google** (the only setup is selecting a support email)
> 3. **Project settings → General → Your apps → Add app → Web** → copy the config snippet. Populate `VITE_FIREBASE_*` env vars from it.
> 4. **Project settings → General → Project ID** → copy → set `FIREBASE_PROJECT_ID` on the backend.
> 5. **Authentication → Settings → Authorized domains** → add the production domain (e.g. `nasrudin.app`) and `localhost` for dev.
> 6. **Authentication → Templates → Email address verification** and **Password reset**: customize subject and body so the emails read "Nasrudin" rather than the default project name.
>
> The API logs `Firebase Auth configured` at startup when `FIREBASE_PROJECT_ID` is set; otherwise `/api/auth/firebase-session` returns 503 and the rest of the API works.

---

## Testing

### Unit tests (Rust)

`engine/crates/api/tests/firebase_verify.rs`:
- `rejects_expired_token` — token with `exp` in the past → `Err(Expired)`.
- `rejects_wrong_audience` — `aud` doesn't match project_id → `Err(WrongAudience)`.
- `rejects_wrong_issuer` — `iss` doesn't match the expected URL → `Err(WrongIssuer)`.
- `rejects_token_signed_with_wrong_key` — token signed with key not in JWKs cache → `Err(BadSignature)`.
- `rejects_malformed_token` — non-JWT input → `Err(MalformedToken)`.
- `accepts_valid_token` — correctly-signed, well-formed token → `Ok(claims)` with expected fields.

Tests use a locally-generated RSA keypair for signing fixtures. `verify_id_token` takes the JWKs cache as an argument so tests can inject a `HashMap<kid, DecodingKey>` directly without HTTP.

### Integration test (Rust)

`engine/crates/api/tests/firebase_session.rs`:
- Build a test app via the existing `test_app::build()` harness with a stub `FIREBASE_PROJECT_ID = "test-project"` and a JWKs cache pre-populated with the test keypair.
- Mint a self-signed token for `{ uid: "fb_user_1", email: "test@example.com", email_verified: true, name: "Test", sign_in_provider: "google.com" }`.
- POST to `/api/auth/firebase-session` → expect 200, `users` row created with matching `firebase_uid`.
- Subsequent `GET /api/auth/me` → expect 200, returns the user.
- Second POST with the same token → expect 200, no duplicate row.
- POST with `email_verified == false` and `sign_in_provider == "password"` → expect 403 `email_not_verified`.
- POST with no `Cookie` after a clean state → expect new session issued.

### Manual test plan

1. Register a fresh email/password account → check inbox for verification email → click link → return to app → confirm signed in via `GET /api/auth/me`.
2. Sign out → `/api/auth/me` returns 401.
3. "Forgot password?" → reset email arrives → set new password → sign in.
4. Sign in with Google (account that has not used the app before) → confirm new `users` row created.
5. Sign in with Google again on the same account → confirm same `users.id` reused.
6. Try to sign in with email/password before clicking the verification link → confirm 403 `email_not_verified` and the "verify your email" alert renders.

No Firebase emulator is required — tests use injected keypairs in CI; manual tests use a real Firebase project (a free dev project is fine).

---

## Migration / Rollout

1. Provision a Firebase project (`nasrudin-dev`, `nasrudin-prod`).
2. Configure providers, authorized domains, email templates.
3. Set `FIREBASE_PROJECT_ID` and `VITE_FIREBASE_*` env vars in the deploy environment.
4. Deploy schema migration `m20260430_000016_firebase_auth` — this wipes any test users that exist locally.
5. Deploy backend + frontend together. The backend with the migration applied will refuse `/api/auth/register` and `/api/auth/login` (those handlers are deleted). The frontend will only call `/api/auth/firebase-session`. There is no overlap window where a stale frontend hits a stale endpoint.
6. Verify the manual test plan against the deployed environment.

No grace period and no dual-auth window are needed because there are no existing accounts to preserve.

---

## Risks

- **Firebase-as-dependency.** The product depends on Google's Firebase service for sign-in. If Firebase has an outage, no one can sign in (existing sessions remain valid until cookie expiry). Mitigation: cookie TTL of 7 days means a Firebase outage of less than ~7 days only locks out new sign-ins, not existing sessions. Acceptable for an academic tool.
- **JWKs fetch failure on first sign-in after deploy.** If the API daemon can't reach Google's JWKs URL (firewall, DNS issue), all sign-ins return 502. Mitigation: pre-warm JWKs at boot (one HTTP call), log a clear error, and surface in the health endpoint. Pre-warming is a one-line change in `main.rs`.
- **Email deliverability.** Firebase's verification and password-reset emails go through Google's SMTP, which generally lands in Gmail and university mailboxes well, but may land in spam for some receivers. Mitigation: documented in `deploy/README.md` as a known issue; the user can later configure a custom SMTP sender via Firebase if needed.
- **Vendor lock-in.** Firebase UIDs are not portable to other providers. If we ever move off Firebase, every `users.firebase_uid` becomes orphaned. Mitigation: `users.email` is the durable identity anchor. A future migration off Firebase would re-provision identities elsewhere keyed on email.
- **Token replay.** A leaked Firebase ID token is valid for up to 1 hour. Mitigation: tokens are exchanged for a session cookie *once*, immediately on receipt, on the `/api/auth/firebase-session` endpoint over HTTPS. The cookie carries no Firebase token; ID token leakage doesn't compromise sessions.

---

## Files touched (estimate)

**Backend (Rust)**
- `engine/crates/pg/src/migrator/m20260430_000016_firebase_auth.rs` (new)
- `engine/crates/pg/src/migrator/mod.rs` (register migration)
- `engine/crates/pg/src/entity/users.rs` (drop password_hash/github_*; add firebase_uid)
- `engine/crates/pg/src/query/users.rs` (`create_firebase_user`; remove `find_or_create_from_github` and old `create_user`)
- `engine/crates/pg/tests/users_oauth_link.rs` (delete)
- `engine/crates/pg/tests/api_keys.rs`, `tests/conjecture_jobs_query.rs` (update `create_user` call sites)
- `engine/crates/api/src/firebase_auth.rs` (new, ~250 lines)
- `engine/crates/api/src/auth.rs` (rewrite `AuthUser`, drop register/login handlers, add `firebase_session` handler)
- `engine/crates/api/src/auth_oauth.rs` (delete)
- `engine/crates/api/src/state.rs` (drop `oauth_github`/`GithubOAuthConfig`; add `firebase_project_id: Option<String>` and `firebase_jwks: Arc<JwksCache>`)
- `engine/crates/api/src/main.rs` (env loading, route changes, JWKs pre-warm)
- `engine/crates/api/src/lib.rs` (drop `auth_oauth`, add `firebase_auth`)
- `engine/crates/api/Cargo.toml` (drop `oauth2`, add `jsonwebtoken`)
- `engine/crates/api/tests/test_app/mod.rs` (drop `oauth_github`, add `firebase_project_id`/JWKs stub, register new route)
- `engine/crates/api/tests/firebase_verify.rs` (new)
- `engine/crates/api/tests/firebase_session.rs` (new)

**Frontend (TS)**
- `nasrudin-frontend/package.json` (add `firebase`)
- `nasrudin-frontend/src/lib/firebase.ts` (new)
- `nasrudin-frontend/src/lib/queries.ts` (rewrite `useLogin`, `useRegister`, `useLogout`; add `useGoogleLogin`, `useResetPassword`, `useResendVerification`)
- `nasrudin-frontend/src/components/auth/AuthForm.tsx` (rewrite — Google primary, forgot-password flow, verification alert)
- `nasrudin-frontend/src/styles/platform.css` (rename `.oauth-primary` to be Google-styled if needed; keep current style but swap the SVG)

**Config / docs**
- `.env.example` (remove GitHub OAuth block; add Firebase block)
- `deploy/README.md` (replace GitHub OAuth section with Firebase section)
