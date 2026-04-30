# Admin Panel & Trust-Bypass Verification — Design

**Date:** 2026-04-30
**Status:** Approved (brainstorming complete, ready for implementation planning)

## 1. Problem & motivation

Two related problems:

1. **Server CPU waste from redundant lake-build.** Workers locally run `lake build`
   before submitting and set `worker_verified=true`. The server's reverify drain
   already accepts this on the chain-replay path (P-Task 1) and flips the row to
   `Verified` instantly. However, the row is *also* enqueued for an
   asynchronous server-side `lake build` confirmation in the lake-promotion drain
   (P-Task 2). For trusted contributors — especially the operator's own workers
   running on the same DigitalOcean droplet as the API — this redundant kernel
   check is the most expensive thing the server does and adds nothing.
2. **No admin tooling.** There is no UI for routine operator tasks: marking
   users as trusted, granting research credits, changing plan tier, refunding
   charges, debugging a user's session, sending a notification, or auditing who
   did what. Everything is hand-rolled SQL or a Bearer-token curl against the
   pre-existing `/api/admin/*` endpoints.

This spec addresses both: a verification-cost optimization for trusted
submissions, plus the admin panel that grants the trust and serves as the
operator's general-purpose console.

## 2. Goals (in scope)

- **Trust bypass.** Skip the server-side eager `lake build` for trusted
  submissions, with sampled spot-check (default 1-in-50) preserving cascade-
  reject and reputation-EMA safety nets.
- **Co-located worker auto-trust.** A unix-domain-socket listener on the API
  process; workers running on the same VM connect via the socket and are
  trusted by transport. Caddy never proxies to the socket.
- **Admin panel.** Frontend route `/admin`, gated by `users.is_admin`. Covers:
  user list/detail, plan tier, credit grants, trust toggle, per-API-key trust
  overrides, API-key revoke, conjecture-job cancel, Stripe refunds, user
  impersonation, custom email send, audit log, bulk operations, surfacing the
  existing `reload_corpus` / `steering_force` endpoints.
- **Audit log.** Every admin mutation transactionally writes a row to
  `admin_audit_log` with `before`/`after` JSONB, required reason, actor, and
  request metadata.
- **Email infrastructure.** Resend-backed transactional + admin-composed
  email, queued in `email_outbox`, retried with exponential backoff, with
  webhook handling for bounces/deliveries.
- **Stripe refunds.** DB-first → Stripe-second flow with idempotency keys,
  reconciler for crash recovery, webhook integration, admin UI affordance.
- **User impersonation.** HMAC-signed time-bounded tokens, persistent UI
  banner, blocked-during-impersonation list for sensitive endpoints, full
  audit trail.

## 3. Goals (explicitly out of scope)

- Worker discovery / WebRTC peer-to-peer routing.
- Bulk import of users.
- 2FA for admin accounts (separate spec when needed).
- Multi-tenancy of the admin panel (a single org's admins).
- Self-service refund-by-user (admin-only).

## 4. Trust resolution & spot-check sampling

### 4.1 Trust resolution order

A new module `engine/crates/api/src/trust.rs` exposes:

```rust
pub struct TrustDecision {
    pub trusted: bool,
    pub spot_check_rate: u32,
    pub source: TrustSource,
}

pub enum TrustSource { UnixSocket, ApiKeyOverride, UserFlag, Default }

pub async fn resolve(
    pg: &DatabaseConnection,
    api_key_row: Option<&api_keys::Model>,
    via_unix_socket: bool,
    env_default_rate: u32,
) -> TrustDecision;
```

Resolution order:

1. If submission arrived via the unix socket → `trusted=true`, source=UnixSocket,
   rate from env default (unless overridden in unit env).
2. Else if `api_keys.trust_override IS NOT NULL` → use that. Rate falls back
   through `api_keys.spot_check_rate → users.spot_check_rate → env default`.
3. Else inherit `users.is_trusted`. Rate same fallback chain.
4. Else default: `trusted=false`, source=Default.

Trust resolution is the only place the boolean is decided. Called from the
`WorkerAuth` extractor and threaded through to `ingest_one_theorem` via request
extensions.

### 4.2 In-memory cache

`dashmap`-backed cache keyed by `api_key_id`. TTL 30s, capacity 4096.
Invalidated on admin trust mutations via a `tokio::sync::broadcast` channel.

### 4.3 Spot-check sampling

In `reverify.rs::process_one`, on the `ChainCheck::Regenerated` branch:

```rust
let should_promote = if !decision.trusted {
    true
} else if decision.spot_check_rate == 0 {
    false                                          // pure trust
} else if decision.spot_check_rate == 1 {
    true                                           // effectively untrusted
} else {
    fnv1a64(theorem_id) % decision.spot_check_rate as u64 == 0
};
```

Hash is deterministic per-theorem-ID so re-runs of the drain pick the same
sampled subset (stability for debugging).

### 4.4 Trusted-bypass verification path

Trusted+sampled-out submissions are flipped directly to:

```
VerificationStatus::Verified { tactic_used: "lake_build", proof_term: vec![] }
```

with `verification_path = "trusted_bypass"` recorded on the row. They become
full peer-axioms in `/api/seed` immediately.

Untrusted and trusted+sampled submissions retain current behavior: enqueued
into the lake-promotion drain at p1. Cascade-reject and reputation-EMA
adjustment continue to fire on disagreements for the sampled subset.

The lazy-lake-on-download path (`handlers/theorems.rs`) is unchanged — if any
external party fetches a `.lean` file from a trusted-bypassed theorem, the
kernel check still fires.

## 5. Unix-domain-socket listener

### 5.1 Server-side

In `engine/crates/api/src/main.rs`, two `axum::serve` calls share the same
`Router`:

- Public TCP `0.0.0.0:3001` (existing).
- Unix socket at `NASRUDIN_LOCAL_SOCK_PATH` (default `/run/nasrudin/api-local.sock`,
  mode 0660, owner `nasrudin:nasrudin`).

A middleware `mark_local_socket_layer` is wrapped *only* around the unix
listener's router. It inserts a `LocalSocket` marker into request extensions.
Public TCP requests cannot reach this middleware → cannot present this marker.
The Caddyfile is unchanged; Caddy proxies only to `127.0.0.1:3001`.

### 5.2 Worker client

The worker binary lives at `engine/crates/ga/src/bin/worker.rs` and currently
reads `NASRUDIN_API_URL` (defaulting to `http://localhost:3001`). The change:
extend its parsing to recognize `unix:///` prefixes and route those through a
`hyper-util` UDS connector. Existing TCP base URLs (`http://...`, `https://...`)
keep their normal `reqwest` connector.

systemd unit `deploy/systemd/nasrudin-worker.service` (the local-droplet
worker) sets:

```
Group=nasrudin
Environment=NASRUDIN_API_URL=unix:///run/nasrudin/api-local.sock
```

If the socket is missing at startup, worker exits 1; systemd restart-policy
retries during deploys.

### 5.3 Authentication via the unix socket

Unix-socket submissions still require an `Authorization: Bearer nsk_worker_…`
header — the existing `WorkerAuth` extractor runs unchanged. The socket only
provides the *trust signal*; it does not replace authentication. We still need
the API key to know:

- which user / worker to record as `contributor_id`,
- which keyed `WorkerRateLimiter` bucket to debit,
- which `users.id` to look up for rate-limit and quota checks.

The `LocalSocket` extension marker only flips the `via_unix_socket` parameter
of `trust::resolve` to `true`; everything else about the request is normal.

## 6. Database schema

Migrations live in `engine/crates/pg/migration/src/`, sequentially numbered
`m20260430_000001` through `m20260430_000008`.

### 6.1 `users` extensions

```sql
ALTER TABLE users ADD COLUMN is_admin BOOLEAN NOT NULL DEFAULT FALSE;
ALTER TABLE users ADD COLUMN is_trusted BOOLEAN NOT NULL DEFAULT FALSE;
ALTER TABLE users ADD COLUMN spot_check_rate INTEGER;
```

`spot_check_rate`: NULL = use env default; 0 = pure trust; 1 = check every; N
= 1-in-N.

### 6.2 `api_keys` extensions

```sql
ALTER TABLE api_keys ADD COLUMN trust_override BOOLEAN;
ALTER TABLE api_keys ADD COLUMN spot_check_rate INTEGER;
```

NULL on either column means inherit from owning user.

### 6.3 `admin_audit_log`

```sql
CREATE TABLE admin_audit_log (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    actor_user_id UUID NOT NULL REFERENCES users(id),
    target_user_id UUID REFERENCES users(id),
    action TEXT NOT NULL,
    before_value JSONB,
    after_value JSONB,
    reason TEXT,
    impersonating_user_id UUID REFERENCES users(id),
    request_ip INET,
    user_agent TEXT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE INDEX admin_audit_log_target ON admin_audit_log (target_user_id, created_at DESC);
CREATE INDEX admin_audit_log_actor ON admin_audit_log (actor_user_id, created_at DESC);
```

Action values are a frozen set of `&'static str` constants (Section 9.2).

### 6.4 `impersonation_sessions`

```sql
CREATE TABLE impersonation_sessions (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    admin_user_id UUID NOT NULL REFERENCES users(id),
    target_user_id UUID NOT NULL REFERENCES users(id),
    started_at TIMESTAMPTZ NOT NULL DEFAULT now(),
    expires_at TIMESTAMPTZ NOT NULL,
    ended_at TIMESTAMPTZ,
    end_reason TEXT,
    reason TEXT NOT NULL
);
CREATE INDEX impersonation_active ON impersonation_sessions (admin_user_id) WHERE ended_at IS NULL;
```

### 6.5 `email_outbox`

```sql
CREATE TABLE email_outbox (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    to_user_id UUID REFERENCES users(id),
    to_address TEXT NOT NULL,
    template TEXT NOT NULL,
    subject TEXT NOT NULL,
    body_text TEXT NOT NULL,
    body_html TEXT,
    status TEXT NOT NULL DEFAULT 'queued',
    attempts INTEGER NOT NULL DEFAULT 0,
    last_attempt_at TIMESTAMPTZ,
    last_error TEXT,
    provider_message_id TEXT,
    queued_by_admin_id UUID REFERENCES users(id),
    queued_by_action TEXT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now(),
    sent_at TIMESTAMPTZ
);
CREATE INDEX email_outbox_pending ON email_outbox (status, created_at)
    WHERE status IN ('queued', 'failed_retrying');
```

`status` values: `queued`, `sent`, `failed_terminal`, `failed_retrying`,
`cancelled_dependent`.

### 6.6 `refund_records`

```sql
CREATE TABLE refund_records (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    user_id UUID NOT NULL REFERENCES users(id),
    admin_user_id UUID NOT NULL REFERENCES users(id),
    stripe_refund_id TEXT UNIQUE,
    stripe_charge_id TEXT NOT NULL,
    amount_cents INTEGER NOT NULL,
    currency TEXT NOT NULL,
    reason TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'pending',
    stripe_failure_reason TEXT,
    requested_at TIMESTAMPTZ NOT NULL DEFAULT now(),
    completed_at TIMESTAMPTZ
);
```

### 6.7 `bulk_runs`

```sql
CREATE TABLE bulk_runs (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    started_by_admin_id UUID NOT NULL REFERENCES users(id),
    action TEXT NOT NULL,
    params JSONB NOT NULL,
    total_count INTEGER NOT NULL,
    completed_count INTEGER NOT NULL DEFAULT 0,
    failed_count INTEGER NOT NULL DEFAULT 0,
    status TEXT NOT NULL DEFAULT 'running',
    started_at TIMESTAMPTZ NOT NULL DEFAULT now(),
    completed_at TIMESTAMPTZ,
    failures JSONB
);
```

### 6.8 Last-admin trigger

```sql
CREATE OR REPLACE FUNCTION prevent_last_admin_demotion() RETURNS TRIGGER AS $$
BEGIN
    IF OLD.is_admin = TRUE AND NEW.is_admin = FALSE THEN
        IF (SELECT count(*) FROM users WHERE is_admin = TRUE AND id != OLD.id) = 0 THEN
            RAISE EXCEPTION 'cannot demote last admin' USING ERRCODE = 'P0001';
        END IF;
    END IF;
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER users_last_admin_guard
    BEFORE UPDATE ON users
    FOR EACH ROW WHEN (OLD.is_admin = TRUE AND NEW.is_admin = FALSE)
    EXECUTE FUNCTION prevent_last_admin_demotion();
```

## 7. Backend admin API

### 7.1 RequireAdmin extractor

`engine/crates/api/src/admin/require_admin.rs`. Order of attempts:

1. Session-based: `AuthSession<Backend>` → if user `is_admin=true` → pass with
   `AdminAuthSource::Session`.
2. Bearer-based: `Authorization: Bearer ADMIN_TOKEN` → pass as system actor
   (`00000000-0000-0000-0000-000000000001`) with `AdminAuthSource::BearerToken`.
3. Else 401 `admin_required`.

Existing `reload_corpus` and `steering_force` migrate to use `RequireAdmin` so
they accept session auth and write audit-log rows.

### 7.2 Endpoint surface

```
GET    /api/admin/users
GET    /api/admin/users/{id}
POST   /api/admin/users/{id}/admin
POST   /api/admin/users/{id}/trust
POST   /api/admin/users/{id}/plan
POST   /api/admin/users/{id}/credits
POST   /api/admin/users/{id}/refund
POST   /api/admin/users/{id}/impersonate
POST   /api/admin/impersonate/end
DELETE /api/admin/api_keys/{id}
POST   /api/admin/api_keys/{id}/trust
POST   /api/admin/jobs/{id}/cancel
POST   /api/admin/users/{id}/email
GET    /api/admin/stats
GET    /api/admin/audit
POST   /api/admin/users/bulk
GET    /api/admin/users/bulk/{run_id}/stream    -- SSE
GET    /api/admin/email/outbox
POST   /api/admin/email/{id}/retry

# already exist; reaffirmed:
POST   /api/admin/reload_corpus
GET    /api/admin/steering/recent
POST   /api/admin/steering/force
```

### 7.3 Audit-log invariant

Every mutating admin handler goes through:

```rust
pub async fn perform_audited<F, Fut, T>(
    pg: &DatabaseConnection,
    actor: &AuthUser,
    impersonation: Option<ImpersonationCtx>,
    req_meta: RequestMeta,
    target_user_id: Option<Uuid>,
    action: &'static str,
    reason: String,
    before_value: serde_json::Value,
    mutate: F,
) -> Result<T, AuditError>
where
    F: FnOnce(&DatabaseTransaction) -> Fut,
    Fut: Future<Output = Result<(T, serde_json::Value), DbErr>>;
```

The mutation closure runs inside the same transaction as the audit-log INSERT.
Reason is validated `≥ 10 chars` server-side. No admin endpoint may bypass this
helper. Code-review rule: PRs adding admin endpoints that bypass it are
rejected.

### 7.4 Frozen action taxonomy

Constants in `engine/crates/api/src/admin/audit.rs::actions`:

```
SET_IS_ADMIN, SET_IS_TRUSTED, SET_SPOT_CHECK_RATE, SET_KEY_TRUST,
SET_PLAN_TIER, ADJUST_CREDITS,
REVOKE_API_KEY,
REFUND_INITIATED, REFUND_SUCCEEDED, REFUND_FAILED,
IMPERSONATE_START, IMPERSONATE_END, IMPERSONATE_FORCE_END, IMPERSONATED_ACTION,
CANCEL_JOB,
RELOAD_CORPUS, FORCE_STEERING,
QUEUE_EMAIL, RETRY_EMAIL,
BULK_RUN_START, BULK_RUN_COMPLETE,
AUTO_REVOKE_WORKER
```

`AUTO_REVOKE_WORKER` is the existing reputation-EMA-based auto-revoke logic
in `lake_promotion.rs` gaining audit-log integration — the heuristic that
fires when a worker's EMA crosses the auto-revoke threshold after a
`worker_claim` disagreement. It now writes an audit row using the system
actor instead of fading silently into a tracing log line.

System-written entries (refund reconciler, auto-revoke, expiry tick for
impersonation sessions) use the system actor UUID.

### 7.5 Self-protection guardrails

- Application-level: refuse to `is_admin=false` self.
- Application-level: refuse to impersonate self.
- Application-level: refuse to delete/disable own user record.
- Application-level: during impersonation, all `/api/admin/*` blocked.
- DB-level: `prevent_last_admin_demotion` trigger.
- Bootstrap escape: `ADMIN_TOKEN` Bearer header always works.

## 8. Stripe refunds

### 8.1 Flow

`POST /api/admin/users/{id}/refund` with body `{stripe_charge_id, amount_cents, reason}`:

1. RequireAdmin gate.
2. Validate the charge belongs to this user (`GET /v1/charges/{id}` → assert
   `charge.customer == user.stripe_customer_id`).
3. **In one DB transaction:** insert `refund_records (status='pending')`,
   insert `admin_audit_log (action=REFUND_INITIATED)`, insert `email_outbox
   (template='admin_refund_issued')`. Commit.
4. Call `POST /v1/refunds` with `idempotency_key = refund_records.id` and
   `metadata.refund_record_id = refund_records.id`.
5. On 2xx: update `refund_records` to `succeeded` and store `stripe_refund_id`.
   Email worker sends the queued email.
6. On 4xx: update to `failed`, record `stripe_failure_reason`, mark queued
   email as `cancelled_dependent`.
7. On 5xx/network: leave `pending`. Reconciler resolves.

### 8.2 Reconciler

Module `engine/crates/api/src/billing/refund_reconciler.rs`. Tick every 60s.
For each `refund_records WHERE status='pending' AND requested_at < now() - INTERVAL '90 seconds'`:

1. `GET /v1/refunds?charge={charge_id}` from Stripe.
2. Match by `metadata.refund_record_id`. If found, copy `id` and `status` into
   our row.
3. After 5 minutes from `requested_at` with no resolution, mark `failed` with
   `reconciler_timeout`.

### 8.3 Webhook integration

Extend `engine/crates/api/src/billing/webhook.rs`:

- `charge.refunded` → look up `refund_records WHERE stripe_charge_id=...`,
  update from webhook payload.
- `charge.refund.updated` → same.

## 9. User impersonation

### 9.1 Session model

`POST /api/admin/users/{id}/impersonate` with `{duration_seconds, reason}`:

1. Validate: target exists, target ≠ admin, target `is_admin=false`,
   admin `is_admin=true`.
2. Insert `impersonation_sessions` with `expires_at = now() + duration_seconds`
   (clamped 60s..3600s, default 900s/15min).
3. Audit-log `IMPERSONATE_START`.
4. Mint HMAC-SHA256 token over `{session_id, admin_user_id, target_user_id, expires_at}`
   with `IMPERSONATION_SIGNING_KEY`.
5. Return `{token, expires_at}`. Frontend stores in `sessionStorage`.

### 9.2 Server-side application

Middleware `ImpersonationLayer` runs after the regular auth-session extractor.
On request bearing `X-Impersonate-Token`:

1. Verify HMAC.
2. Look up session row; reject if `ended_at IS NOT NULL` or `expires_at < now()`.
3. Verify session `admin_user_id` matches the underlying logged-in `AuthUser.id`.
4. Replace `AuthUser` with target user's. Insert `Impersonation { session_id,
   original_admin_id }` marker into request extensions.

### 9.3 Blocked endpoints during impersonation

- All `/api/admin/*` → 403 `cannot_during_impersonation`.
- `POST /api/auth/login`, `DELETE /api/auth/logout`.
- `POST /api/api_keys` (no key minting).
- `POST /api/billing/*`.
- `POST /api/preferences`.

Allowed-but-extra-audited: `POST /api/conjecture/*/submit`, `POST /api/jobs/*`.
Each writes `IMPERSONATED_ACTION` audit row with payload summary.

### 9.4 Expiry tick

60s scan: `impersonation_sessions WHERE ended_at IS NULL AND expires_at < now()`
→ set `ended_at, end_reason='expired'`, audit `IMPERSONATE_END`.

### 9.5 UI behavior

Persistent red banner on every page when `sessionStorage.impersonating === '1'`,
ticks countdown. At zero, frontend calls `POST /api/admin/impersonate/end`,
clears sessionStorage, redirects to `/admin`.

## 10. Email infrastructure (Resend)

### 10.1 Provider

Resend (`api.resend.com`). Justification: trivial REST API (no SDK needed),
single API-key auth, free tier covers expected volume, easy DKIM via DNS
records.

### 10.2 Module structure

```
engine/crates/api/src/email/
├── mod.rs              -- public surface: queue(), spawn_worker()
├── outbox.rs           -- DB CRUD on email_outbox
├── provider.rs         -- trait EmailProvider; impl ResendProvider
├── templates.rs        -- Tera template registry
├── worker.rs           -- async drain loop
└── templates/          -- *.html, *.txt files
    ├── admin_credit_grant.{html,txt}
    ├── admin_plan_change.{html,txt}
    ├── admin_refund_issued.{html,txt}
    ├── admin_account_action.{html,txt}
    └── admin_custom_message.{html,txt}
```

### 10.3 Drain loop

Polls every 5s for `status IN ('queued', 'failed_retrying') AND attempts < 5
AND (last_attempt_at IS NULL OR last_attempt_at < now() - INTERVAL '5 min' * pow(2, attempts))`.
Concurrency-limited by `Semaphore::new(4)`.

Outcomes:
- 2xx → `sent`, store `provider_message_id`.
- 4xx → `failed_terminal`.
- 5xx / network → `failed_retrying`, attempts++. Caps at 5 attempts then
  `failed_terminal`.

### 10.4 Webhook intake

`POST /api/webhook/resend`:

1. Verify HMAC against `RESEND_WEBHOOK_SECRET`.
2. On `email.bounced` / `email.complained` → set `failed_terminal`.
3. On `email.delivered` → no-op (already `sent`).
4. Bounces against a user's address surface in their admin detail page as a
   "deliverability warning" badge.

### 10.5 Transactional coupling for system emails

System-triggered emails (credit grant, plan change, refund issued, account
action) are queued *inside the same DB transaction* as the mutating change via
`email::queue_in_txn(&txn, ...)`. If the email queue insert fails, the whole
admin action rolls back.

Admin-composed emails (`admin_custom_message`) skip this coupling — the audit
log records the attempt; outbox UI shows delivery status.

### 10.6 DNS

Documented in `deploy/scripts/email-dns-setup.md`:
- SPF: `v=spf1 include:_spf.resend.com -all`
- DKIM: 3 CNAMEs from Resend dashboard for `nasrudin.org`
- DMARC: `v=DMARC1; p=none; rua=mailto:postmaster@nasrudin.org`

## 11. Frontend admin panel

### 11.1 Route tree

```
nasrudin-frontend/src/routes/
├── admin.tsx
├── admin.index.tsx
├── admin.users.tsx
├── admin.users.$id.tsx
├── admin.audit.tsx
├── admin.impersonations.tsx
├── admin.email.tsx
├── admin.steering.tsx
├── admin.corpus.tsx
└── admin.bulk.tsx
```

`admin.tsx` has a `beforeLoad` that hits `GET /api/admin/users?page_size=1`; on
403 redirects to `/`. `__root.tsx` adds `is_admin` to `GET /api/me` and
conditionally renders the "Admin" nav link.

### 11.2 Component infrastructure

`nasrudin-frontend/src/components/admin/`:

- `<DataTable />` — sortable, server-paginated, URL-bound filters; reused by
  user list, audit log, email outbox, impersonations.
- `<ConfirmWithReasonModal />` — required reason field (≥10 chars), shared
  across all mutations. The only path admin mutations take.
- `<ImpersonationBanner />` — sticky red banner with countdown.

### 11.3 User detail tabs

`/admin/users/$id` tab strip: Overview, Trust, Billing, API Keys, Audit, Email.
Impersonate button is pinned to the page header (not a tab).

### 11.4 Bulk runner

`/admin/bulk` reads selected user IDs from URL query (small N) or
sessionStorage (large N), shows per-user dry-run preview, runs serial
operation streamed via SSE on `GET /api/admin/users/bulk/{run_id}/stream`.

## 12. Stats endpoint

`GET /api/admin/stats` runs the following in `tokio::join!`:

- Total users, paid users, active in 24h.
- Theorems by status.
- Reverify queue depth, lake-promotion queue depth, email outbox pending.
- Trust stats: total trusted users, total trusted keys, trusted-bypass
  submissions / sampled / cascade-rejected in last 24h.
- Recent audit log (last 10).

Cached in `state.stats_cache: ArcSwap<(Instant, StatsResponse)>` for 10s.

## 13. Trust cache & invalidation

`engine/crates/api/src/trust.rs` holds:

```rust
pub struct TrustCache {
    inner: dashmap::DashMap<Uuid, (Instant, TrustDecision)>,
}
```

TTL 30s, capacity 4096 (LRU on insert if full). Mutating admin endpoints
broadcast on `tokio::sync::broadcast::Sender<CacheInvalidation>` after committing;
the cache subscribes and purges affected entries.

## 14. Bulk run execution

`POST /api/admin/users/bulk` returns `{run_id}` immediately. Handler `tokio::spawn`s:

1. INSERT `bulk_runs` row.
2. Iterate user_ids serially. Each iteration calls the same per-user logic
   (extracted into a shared non-handler function) so each step audit-logs
   exactly as a per-user call would.
3. After each user, UPDATE `bulk_runs` counters; broadcast on the per-run SSE
   channel.
4. On completion, set `bulk_runs.status='completed'`, populate `failures`
   JSONB, audit `BULK_RUN_COMPLETE`.

Failures don't abort. UI lets admin re-target failed-only users.

API-process restart reaper: at startup, mark any `bulk_runs WHERE status='running'
AND started_at < now() - INTERVAL '1 hour'` as `aborted`.

## 15. Error handling & response shape

Uniform error body:

```json
{ "error": "snake_case_code", "message": "...", "details": { ... } }
```

Status codes: 400 validation, 401 unauthenticated, 403 not-admin/blocked-during-
impersonation/expired, 404 not-found, 409 state-conflict, 422 Stripe-rejected,
500 unhandled, 502 upstream, 503 PG-unavailable.

Frontend catches at a shared `adminApi.ts` wrapper; toasts errors;
on `403 admin_required` redirects to `/`.

## 16. Testing

### 16.1 Backend (Rust)

- Trust resolution: 6 unit tests covering source priority and rate fallback.
- Reverify spot-check sampling: 5 integration tests with faked lake-builder.
- Audit invariant: 4 tests covering atomic commit/rollback and reason
  validation.
- Impersonation middleware: 6 tests covering token validation, expiry,
  admin-binding, blocked endpoints.
- Refund flow: 6 tests including `wiremock`-faked Stripe.
- Bulk runner: 3 tests including restart reaper and SSE progress.
- Email worker: 3 tests covering 4xx/5xx/webhook.
- RequireAdmin: 4 tests covering session, token, mismatched.
- Last-admin trigger: 2 DB integration tests.

### 16.2 Frontend

- Component tests (Vitest): `<ConfirmWithReasonModal />`, `<DataTable />`,
  `<ImpersonationBanner />`.
- E2E (Playwright, seeded test DB): admin trust toggle round-trip,
  impersonation start-to-expire, bulk run with SSE.

### 16.3 Property tests (proptest)

- Trust resolution determinism.
- Spot-check sampling uniformity (within ±5% of `1/N` over 10k samples).
- Audit JSONB serialization total-ness.

### 16.4 Manual QA

- Chaos test: kill API mid-refund, confirm reconciler resolves.
- Unix socket from co-located worker: confirm trust applied.
- Public TCP via Caddy: confirm no auto-trust.
- Each email template: confirm rendering.

## 17. Rollout

1. Run PG migrations (`just db:migrate`).
2. Deploy API.
3. `deploy/scripts/admin-bootstrap.sh nasrudin.salim.suden@gmail.com` — sets
   first admin, creates system actor.
4. Add SPF/DKIM/DMARC DNS records.
5. Set `RESEND_API_KEY`, `RESEND_WEBHOOK_SECRET`, `IMPERSONATION_SIGNING_KEY`,
   `EMAIL_FROM`, `EMAIL_REPLY_TO`, `TRUSTED_SPOT_CHECK_RATE` in
   `/etc/nasrudin/api.env`.
6. Configure Resend webhook URL in Resend dashboard:
   `https://api.nasrudin.org/api/webhook/resend`.
7. Deploy frontend.
8. Update `deploy/systemd/nasrudin-worker.service` for the local worker:
   `Group=nasrudin`, `Environment=NASRUDIN_API_URL=unix:///run/nasrudin/api-local.sock`.
   Restart. Confirm submissions arrive trusted.

Each step is independently reversible. Schema changes are additive — old
binary keeps working with new columns.

## 18. Observability

Prometheus metrics added to `metrics.rs`:

```
trust_lookup_total{decision, source}
trust_cache_hits_total
trust_cache_misses_total
spot_check_decisions_total{action}
spot_check_disagreements_total
admin_action_total{action, outcome}
impersonation_active_sessions
email_queue_depth{status}
email_send_attempts_total{outcome}
refund_records_total{status}
refund_reconciler_resolved_total
bulk_runs_active
bulk_runs_completed_total{outcome}
```

## 19. Configuration

New env vars on `nasrudin-api.service`:

```
TRUSTED_SPOT_CHECK_RATE=50
NASRUDIN_LOCAL_SOCK_PATH=/run/nasrudin/api-local.sock
RESEND_API_KEY=re_...
RESEND_WEBHOOK_SECRET=whsec_...
IMPERSONATION_SIGNING_KEY=<64 hex bytes>
EMAIL_FROM=Nasrudin <noreply@nasrudin.org>
EMAIL_REPLY_TO=support@nasrudin.org
ADMIN_TOKEN=<existing — bootstrap escape>
```

## 20. Documentation deliverables

- Update `README.md` admin section with bootstrap command + URL.
- New `docs/admin/runbook.md`: revoke, refund, custom email, spot-check
  disagreement interpretation.
- New `deploy/scripts/email-dns-setup.md`: SPF/DKIM/DMARC.
- Update `CLAUDE.md` engine workspace map with new `email/` and `admin/`
  modules.

## 21. Bootstrap script

`deploy/scripts/admin-bootstrap.sh`:

```bash
#!/usr/bin/env bash
set -euo pipefail
EMAIL="${1:?email required}"
psql "$NASRUDIN_DATABASE_URL" <<SQL
UPDATE users SET is_admin = TRUE WHERE email = '$EMAIL';
INSERT INTO users (id, email, password_hash, plan_tier, is_admin, created_at)
VALUES (
    '00000000-0000-0000-0000-000000000001',
    'system@nasrudin.org',
    'unusable!',
    'free',
    TRUE,
    now()
) ON CONFLICT (email) DO NOTHING;
SQL
```

## 22. Open questions

None. All design decisions ratified during brainstorming:

- Trust granularity: user-level with per-API-key override.
- Co-location detection: unix socket only (no TCP loopback heuristics).
- Spot-check rate: env-default + per-user + per-key override.
- Admin auth: `users.is_admin` + session, with `ADMIN_TOKEN` bootstrap.
- Email provider: Resend.
- Refund flow: DB-first, idempotency keys, reconciler.
- Impersonation: HMAC + sessionStorage, blocked-on-sensitive list.
- Audit invariant: single helper, transactional, no exceptions.
- Bulk operations: SSE-streamed serial execution, no abort-on-failure.
