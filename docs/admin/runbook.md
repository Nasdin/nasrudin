# Admin runbook

The admin panel lives at `/admin`. Access is gated by `users.is_admin`
or by sending `Authorization: Bearer $ADMIN_TOKEN` (system actor).

## Bootstrap

After your first deploy, sign in once via the regular Firebase flow so
your `users` row exists, then promote yourself:

```
NASRUDIN_DATABASE_URL=postgres://... \
  deploy/scripts/admin-bootstrap.sh you@example.com
```

The script also creates the **system actor** row with id
`00000000-0000-0000-0000-000000000001`. The refund reconciler, the
60-second impersonation expiry tick, and the worker auto-revoke logic
all use this id as the `actor_user_id` for system-driven audit rows.

## Daily quick-checks

- `/admin` — `users_total`, `theorems_by_status`, queue depths.
- `/admin/audit` — recent admin actions.

## Mark a user trusted (skip server-side `lake build`)

1. `/admin/users` → click email.
2. Trust tab → toggle "Trusted" → enter reason (≥ 10 chars).
3. Audit row written; trust cache invalidated; the next submission
   from any of that user's worker keys flows through the
   trusted-bypass path (verification_path = `trusted_bypass`).

## Per-key trust override

Use this when you want a single co-located worker key to be trusted
without flipping the user's blanket trust. `/admin/users/{id}` → Keys
tab → set `trust_override = true`.

## Spot-check rate

`spot_check_rate` controls 1-in-N sampling for trusted submissions.
NULL = use env default (`TRUSTED_SPOT_CHECK_RATE`); 0 = pure trust;
1 = effectively untrusted; N>1 = sample every Nth.

## Revoke an API key

`/admin/users/{id}` → Keys → Revoke → reason. Cache invalidates
immediately.

## Issue a refund (Stripe)

`/admin/users/{id}` → Billing → Refund. Provide `ch_...` and amount in
cents. Flow:
1. We INSERT `refund_records (status='pending')` + audit row in one txn.
2. We POST `/v1/refunds` to Stripe with `Idempotency-Key = refund_records.id`.
3. 2xx → mark succeeded; 4xx → mark failed; 5xx → leave pending,
   the **reconciler** (60s tick) resolves it within 90 seconds.

Stripe sends the user-facing "Refund Issued" email automatically. We
do not queue any user email.

## Bulk operations

`/admin/bulk`. Paste user IDs (one UUID per line), pick action, set
params JSON, give a reason. SSE-streamed progress; failures don't
abort the run.

## Impersonate

`/admin/users/{id}` → Impersonate. 15-minute default duration;
clamped 60 s — 3600 s. Frontend stores the HMAC-signed token in
`sessionStorage` and shows a sticky red banner with countdown.
End-of-session: click "End impersonation" or wait for expiry.

Cannot impersonate yourself. Cannot impersonate another admin.

## Reload corpus

`/admin/corpus` → "Reload corpus". Reads `prover/../physlean-extract/output/`
catalogs and hot-swaps the AxiomStore. Workers see the new building
blocks on their next `/api/seed` poll.

## Spot-check disagreement

When a trusted+sampled-in submission goes through lake-promotion and
the kernel disagrees, the worker's reputation EMA tanks. At EMA < 0.2
the auto-revoke logic in `lake_promotion.rs` revokes the offending
api_key and writes an `AUTO_REVOKE_WORKER` audit row using the system
actor.

## Last-admin protection

DB trigger `users_last_admin_guard` blocks demoting the only admin
row. To recover: SSH to the droplet and `INSERT` another admin
`users` row by hand. Then redeploy.
