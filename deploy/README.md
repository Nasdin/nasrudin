# Deploy

Operational notes for running the API + frontend in production.

Most of the moving pieces are documented inline in their unit / config files
(`systemd/*.service`, `Caddyfile.native`, `scripts/`). This README is for
ops decisions that don't fit cleanly anywhere else.

## Firebase Auth (sign-in)

Sign-in is powered by Firebase Authentication. To bring up a fresh
environment:

1. Visit <https://console.firebase.google.com> → **Add project** → name it
   (e.g. `nasrudin`, `nasrudin-staging`).
2. **Authentication → Get started** → enable two providers:
   - **Email/Password** — leave "Email link (passwordless sign-in)" off.
   - **Google** — pick a support email from the dropdown.
3. **Project settings → General → Your apps → Add app → Web** → register
   the web app. Copy the Firebase SDK config snippet — populate the
   `VITE_FIREBASE_*` env vars from it.
4. **Project settings → General → Project ID** — copy → set
   `FIREBASE_PROJECT_ID` on the backend.
5. **Authentication → Settings → Authorized domains** — add the production
   domain (e.g. `nasrudin.app`) and `localhost` for dev.
6. **Authentication → Templates → Email address verification** and
   **Password reset** — customize subject and body so emails read "Nasrudin"
   rather than the default Firebase project name.

The API logs `Firebase Auth configured` at startup when `FIREBASE_PROJECT_ID`
is set; otherwise `/api/auth/firebase-session` returns 503 and the rest of
the API works (worker keys and live API keys continue to function).

The first sign-in attempt after `FIREBASE_PROJECT_ID` is set fetches
Google's signing keys (one HTTP round-trip, ~200ms). The API pre-warms
the cache at boot in the background; failures are logged and recovery is
automatic on next sign-in.

## Stripe sponsor prices

Operators must set the four sponsor price ids alongside the standard
Researcher prices. The fourth (`STRIPE_PRICE_SPONSOR_OPEN`) backs the
"Custom amount" donation tile on `/sponsor`: it points at a Stripe Price
with `unit_amount=null` and is wired into a Checkout Session with
`mode=payment` + `submit_type=donate`, so the hosted page presents an
amount input. Pricing today (production):

```
STRIPE_PRICE_SPONSOR_5=price_1TRj8B...   # $5 / month subscription
STRIPE_PRICE_SPONSOR_25=price_1TRj8C...  # $25 / month subscription
STRIPE_PRICE_SPONSOR_100=price_1TRj8D... # $100 / month subscription
STRIPE_PRICE_SPONSOR_OPEN=price_1TRj8P...# one-time, customer-adjustable
```

These live in `~/.nasrudin-stripe.env` on the production droplet and are
not checked into the repo. Operators who add `SPONSOR_OPEN` for the
first time should restart the API after writing the env var; no
migration is needed for the price itself.

Sponsorships and one-time donations are recorded in the
`user_sponsorships` table by the Stripe webhook
(`/api/billing/webhook` — `customer.subscription.{created,updated,deleted}`
and `checkout.session.completed` with `mode=payment`). The public
profile reads from this table via `summary_for_user` to render badges.
A one-shot backfill from Stripe is available behind
`BACKFILL_SPONSORSHIPS=1` for cold-starting an environment that already
has live customers.
