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

## Provisioned resources

Both modes (test + live) are set up. Concrete product / price / Payment
Link IDs are in the gitignored env files (this repo is public):

- **Local dev (test mode):** `.env` at repo root.
- **Production (live mode):** `deploy/.env` on the droplet (also kept
  gitignored locally if you keep a copy for ops).

Resource shape in each mode:

| What                  | Recurring                                     |
|-----------------------|-----------------------------------------------|
| Researcher product    | One product, two recurring prices ($19/mo, $182.40/yr) |
| Sponsor product       | One product, three recurring prices ($5 / $25 / $100 monthly) + one custom-amount one-time price + one hosted Payment Link |
| Customer Portal       | Default config (cancel-at-period-end, plan switch, payment-method update, invoice history) |

To inspect the exact IDs:

```bash
# In Stripe MCP-enabled CLI / Claude Code:
#   list_products / list_prices

# Or via API:
curl -u $STRIPE_SECRET_KEY: https://api.stripe.com/v1/products
curl -u $STRIPE_SECRET_KEY: 'https://api.stripe.com/v1/prices?product=prod_…'
```

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

Required (drive `users.plan_tier` + period rollover via `webhook::dispatch`):

- `customer.subscription.created`
- `customer.subscription.updated`
- `customer.subscription.deleted`

Archived for forensics in `billing_events` (dispatcher is a no-op for these,
but they're useful when reconstructing what happened to a customer):

- `customer.subscription.paused`
- `customer.subscription.resumed`
- `invoice.payment_succeeded` (interchangeable with `invoice.paid` —
  Stripe fires both for the same condition)
- `invoice.payment_failed`
- `checkout.session.completed`

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

### Production rollout (droplet)

Live products / prices / Payment Link are already provisioned (see table
above) and the IDs are committed to `deploy/.env.example`. What's left:

1. **SSH into the droplet** and edit `/opt/nasrudin/deploy/.env` (or
   wherever `docker-compose.yml` reads from). Add:
   ```
   STRIPE_SECRET_KEY=sk_live_…             # from dashboard.stripe.com/apikeys (Live mode)
   STRIPE_WEBHOOK_SECRET=whsec_…           # from step 2 below
   ```
   The price IDs and redirect URLs are already in `.env.example`; copy
   them through unless you've changed them.

2. **Create the live webhook endpoint**:
   - Dashboard → Developers → Webhooks → Add endpoint
   - URL: `https://api.nasrudin.org/api/billing/webhook`
   - Events: `customer.subscription.created`, `customer.subscription.updated`,
     `customer.subscription.deleted`, `invoice.paid`, `invoice.payment_failed`
   - Copy the signing secret (`whsec_…`) into `STRIPE_WEBHOOK_SECRET` from step 1.

3. **Configure Customer Portal in live mode** (Settings → Billing → Customer
   portal). Match what we did in test:
   - Allow cancellation: at end of period
   - Allow plan switching: monthly ↔ annual
   - Allow payment-method updates
   - Show invoice history
   - Default return URL: `https://nasrudin.org/profile`

4. **Enable Stripe Tax** (Settings → Tax → enable). Required so EU/UK VAT
   is collected on Checkout. Add tax registrations as you cross thresholds.

5. **Activate payment methods** if needed (Settings → Payment methods).
   At minimum cards must be on; Apple Pay / Google Pay / Link are
   recommended for conversion. Currently the live Sponsor Payment Link is
   `card`-only because that's all that was active when it was created;
   recreate it with broader `payment_method_types` once more methods are on.

6. **Restart the API service** so the new env vars get read:
   ```
   sudo systemctl restart nasrudin-api    # native systemd
   # or
   docker compose -f /opt/nasrudin/deploy/docker-compose.yml up -d api
   ```

7. **Smoke-test with a real card**:
   - Visit `https://nasrudin.org/pricing`, click Researcher → Start subscription.
   - Use your own card (or stripe-cli `trigger` against live mode if you
     don't want real charges; but reverse them via dashboard refund).
   - Verify in psql that `users.plan_tier` flipped to `researcher` and
     `current_period_end` is set ~1 month out.

### Switching back to test mode (local dev)

`.env` (project root) holds the test-mode IDs already. `just dev-engine`
reads it. The `deploy/.env.example` only affects the droplet.

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
