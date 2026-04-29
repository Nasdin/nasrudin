# Billing — Stripe Operations Runbook

What you need to know to run, debug, and operate Nasrudin's monetization plumbing.

---

## TL;DR

- **All paid plans go through Stripe.** No payment data ever touches our DB.
- **Plan tier is mirrored to `users.plan_tier`** by webhook. Quotas are enforced from this column.
- **One Stripe Product, two Prices** (Researcher monthly + annual) for Phase 1 self-serve.
- **Webhook idempotency** is keyed on `stripe_event_id` in `billing_events` — replays are safe.
- **Without Stripe env vars**, `/api/billing/*` returns 503 and the rest of the API works fine. Local dev does not require Stripe.

---

## Environment variables

| Var                                  | Purpose                                                        |
|--------------------------------------|----------------------------------------------------------------|
| `STRIPE_SECRET_KEY`                  | `sk_test_…` (dev) / `sk_live_…` (prod). Authenticates the API.  |
| `STRIPE_WEBHOOK_SECRET`              | `whsec_…` from the webhook endpoint config. HMAC verify key.    |
| `STRIPE_PRICE_RESEARCHER_MONTHLY`    | `price_…` for the $19/mo Researcher Price.                      |
| `STRIPE_PRICE_RESEARCHER_ANNUAL`     | `price_…` for the $182.40/yr Researcher Price.                  |
| `STRIPE_CUSTOMER_PORTAL_RETURN_URL`  | Where the portal sends users on close.                          |
| `STRIPE_CHECKOUT_SUCCESS_URL`        | Where Checkout redirects on success.                            |
| `STRIPE_CHECKOUT_CANCEL_URL`         | Where Checkout redirects on cancel.                             |

Setting any of these wrong won't crash the boot — `BillingClient::from_env()` returns `None` and `/api/billing/*` returns 503 with `billing_unavailable`.

---

## First-time setup (Stripe dashboard, test mode)

**Test-mode resources are already provisioned for this project** (test API
key + product + prices live in `.env`):

| Resource             | Test-mode id                                |
|----------------------|---------------------------------------------|
| Product              | `prod_UQY6z9ugEnCRRI` (Nasrudin Researcher)  |
| Price (monthly)      | `price_1TRh0fDrlrOn1hRGpS3INgKd` ($19/mo)    |
| Price (annual, −20%) | `price_1TRh0kDrlrOn1hRGOzY2xrpo` ($182.40/yr)|
| Portal configuration | `bpc_1TRh0sDrlrOn1hRGULhEcLiF` (default)     |

To re-create them from scratch (e.g. on a fresh test-mode account):

```bash
# Product
curl -u $STRIPE_SECRET_KEY: https://api.stripe.com/v1/products \
  -d "name=Nasrudin Researcher" \
  -d "metadata[plan_tier]=researcher"

# Prices (use the product id from above)
curl -u $STRIPE_SECRET_KEY: https://api.stripe.com/v1/prices \
  -d "product=prod_…" -d "currency=usd" -d "unit_amount=1900" \
  -d "recurring[interval]=month" -d "lookup_key=researcher_monthly"

curl -u $STRIPE_SECRET_KEY: https://api.stripe.com/v1/prices \
  -d "product=prod_…" -d "currency=usd" -d "unit_amount=18240" \
  -d "recurring[interval]=year" -d "lookup_key=researcher_annual"
```

**Enable Stripe Tax** (Settings → Tax in dashboard). Required for EU VAT.

**Webhook secret for local dev:**

```bash
stripe listen --forward-to localhost:3001/api/billing/webhook
# Prints a fresh whsec_… valid for the duration of the listener.
# Paste into .env as STRIPE_WEBHOOK_SECRET, then restart `just dev-engine`.
```

**For production:** create a real webhook endpoint in the live-mode dashboard
pointing at `https://<host>/api/billing/webhook`. Subscribe to:

- `customer.subscription.created`
- `customer.subscription.updated`
- `customer.subscription.deleted`
- `invoice.paid`
- `invoice.payment_failed`

Save the signing secret as `STRIPE_WEBHOOK_SECRET` in production env.

---

## End-to-end smoke test

1. Sign up a fresh user in the frontend.
2. Confirm in psql:
   ```sql
   SELECT email, plan_tier, stripe_customer_id FROM users WHERE email='you@example.com';
   ```
   Expect `plan_tier='free'`, `stripe_customer_id IS NULL`.
3. Try `POST /api/conjecture` — expect HTTP 402 `targeted_search_quota_exhausted`.
4. Visit `/pricing`, click "Start subscription", complete Checkout with `4242 4242 4242 4242` / any future expiry / any CVC.
5. Wait ≤2 seconds, refresh `/profile`. Expect:
   - `plan_tier='researcher'`
   - `current_period_end` set ~1 month out
   - 0 / 10 targeted searches used
6. Repeat `POST /api/conjecture` — expect 200.
7. Click "Manage billing" → cancel subscription in the portal.
8. The cancellation fires `customer.subscription.deleted` immediately if you click "Cancel immediately"; for "Cancel at period end" the event fires at period_end.
9. After the event lands, `plan_tier` flips back to `free`.

---

## Operational tasks

### Production rollout (test → live)

1. Re-run dashboard setup in **Live mode** — Products, Prices, Customer Portal config, webhook endpoint all need to be recreated; test-mode objects don't carry over.
2. Swap env vars on the production deployment:
   ```
   STRIPE_SECRET_KEY=sk_live_…
   STRIPE_WEBHOOK_SECRET=whsec_… (from the live-mode webhook endpoint)
   STRIPE_PRICE_RESEARCHER_MONTHLY=price_… (live)
   STRIPE_PRICE_RESEARCHER_ANNUAL=price_… (live)
   ```
3. Deploy. The first Checkout session opened against the live keys creates a real Stripe Customer for the user.
4. Verify the live webhook delivers by triggering a test in the dashboard or running through a real signup with a real card.

### Pricing changes

- Stripe Prices are **immutable** once attached to a subscription. To change the price:
  1. Create a new Price under the same Product.
  2. Update env vars to point at the new Price ids.
  3. New subscriptions get the new price; existing subscriptions stay on their original price (grandfathered).
  4. To migrate existing customers, schedule a Stripe Subscription update via API or manually in the dashboard.

### A webhook event was dropped / failed

1. Find the event id in our DB:
   ```sql
   SELECT stripe_event_id, event_type, received_at, processed_at, process_error
   FROM billing_events
   WHERE processed_at IS NULL
   ORDER BY received_at DESC LIMIT 50;
   ```
2. Or in the Stripe dashboard: Developers → Webhooks → click the endpoint → see "Failed events" tab → "Resend".
3. Resends are idempotent on our side — `record_event_if_new` returns `false` for replays, but we'll still hit the dispatch path on a fresh-after-failure delivery (because the previous row had `processed_at IS NULL`).

### "Did we charge this user yet?"

```sql
SELECT u.email, u.plan_tier, u.stripe_customer_id, u.stripe_subscription_id,
       u.plan_cycle_start, u.current_period_end
FROM users u
WHERE u.id = $user_id;
```

For invoice-level detail, query Stripe directly via the dashboard — we do **not** mirror invoices.

---

## Architecture summary

```
                        ┌─ POST /api/billing/checkout ───┐
                        │  → BillingClient::create_*     │
Browser ─/pricing → ────┤                                ├──→ Stripe Checkout
                        └─ user.stripe_customer_id        │
                           persisted in users table       │
                                                          ↓
                                                Stripe hosts the form

Stripe ─── customer.subscription.created/updated/deleted ──┐
       └── invoice.paid / invoice.payment_failed ──────────┤
                                                           ↓
                          POST /api/billing/webhook
                                  │
                                  ├─ verify HMAC over `<t>.<body>`
                                  ├─ insert into billing_events (idempotent)
                                  ├─ dispatch by event_type
                                  │     subscription.* → apply_subscription_active
                                  │                    → apply_subscription_cancelled
                                  └─ mark billing_events.processed_at

users.plan_tier ──→ AuthOrApiKey extractor exposes PlanTier
                ──→ PlanTier::quotas() drives:
                      • conjecture::create gate (targeted searches)
                      • api_quota_layer middleware (api_per_day)
```

---

## Files

| File                                                   | Role                                            |
|--------------------------------------------------------|-------------------------------------------------|
| `engine/crates/api/src/billing/tier.rs`                | `PlanTier` enum, `Quotas`, `period_start`       |
| `engine/crates/api/src/billing/stripe_client.rs`       | async-stripe wrapper (Customer / Checkout / Portal) |
| `engine/crates/api/src/billing/webhook.rs`             | typed Webhook::construct_event + dispatch       |
| `engine/crates/api/src/billing/api_quota_layer.rs`     | per-day request middleware                      |
| `engine/crates/api/src/handlers/billing.rs`            | checkout / portal / me / webhook handlers       |
| `engine/crates/pg/src/query/billing.rs`                | webhook idempotency + sub-state mutators        |
| `engine/crates/pg/src/query/targeted_search_usage.rs`  | targeted-search counter                         |
| `engine/crates/pg/src/query/api_usage.rs`              | atomic daily-count UPSERT                       |
| `engine/crates/pg/src/migrator/m20260429_000009_*.rs`  | the four billing migrations                     |
| `nasrudin-frontend/src/routes/pricing.tsx`             | tier ladder + checkout wiring                   |
| `nasrudin-frontend/src/routes/profile.tsx`             | BillingCard (plan / usage / Manage billing)     |
