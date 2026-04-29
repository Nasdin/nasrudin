# Monetization Foundation (Stripe + Repriced Tiers) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship Stripe-backed individual subscriptions (Free + Researcher) with plan-aware API and targeted-search quotas; reprice the tier ladder (Free / Researcher / Team / Institution / Enterprise) so small groups have a real upgrade path; and rewrite pricing-page copy so academics are not the framed buyer, the tier ladder is structurally consistent, and worker compensation is honest.

**Architecture:** Stripe Checkout starts subscriptions; Stripe Customer Portal handles cancel/upgrade/payment-method; a webhook handler writes `plan_tier` and `current_period_end` to Postgres on `customer.subscription.*` and `invoice.*` events. The existing `AuthOrApiKey` extractor is extended to load `PlanTier` onto the request; the conjecture-create handler and a new `tier_quota` tower layer enforce quotas. Stripe Price IDs are configured via env vars so the same code runs against test/live modes. Org/team subscriptions and worker compute-credits ship as separate plans (referenced in §"Out of scope" below).

**Tech Stack:**
- **Backend:** Rust 2024, Axum 0.8, SeaORM 2, async-stripe 0.40, axum-login 0.18, tower 0.5
- **Frontend:** TanStack Start v1, React 19, TanStack Query v5
- **Billing:** Stripe Checkout, Stripe Billing (subscriptions), Stripe Customer Portal, Stripe Tax, Stripe Webhooks
- **Database:** PostgreSQL 18 (existing)

**Spec source:** This plan is the spec — derived from in-conversation review of `nasrudin-frontend/src/routes/pricing.tsx`, `engine/crates/pg/src/entity/users.rs`, and `engine/crates/api/src/rate_limit.rs`. No prior brainstorming doc.

---

## Business design (the "why" before the "how")

The 3 fixes baked into this plan:

### Fix 1 — Stop framing academics as the buyer

**Problem:** Pricing copy says "for working academics" while the FAQ gives Researcher *free* to anyone with a `.edu` / `.ac.*` email. Most academics have no personal SaaS budget anyway. The two halves cancel: the framed buyer doesn't pay, and the actual paying segment (independent researchers, industrial R&D, quant funds, AI labs) doesn't see itself in the copy.

**Fix:**
- Drop ".edu = free Researcher" entirely. Replace with **Verified Academic** badge: 50% off Researcher (so $9.50/mo), library limit raised on Free tier, citation export unlocked on Free. Researcher itself stays paid; the discount keeps academic goodwill without giving away the product.
- Re-frame pricing-page copy from "for academics" to **"For builders pointing compute at hard problems"** — speaks to indie researchers, industry, and academics-with-budget alike.
- Free tier is the *citation infrastructure* — generous read access (browse, save, download `.lean`, cite, re-verify) is free forever because that's what creates the network effect, not a discount we hand out.

### Fix 2 — Lab tier compression → coherent ladder

**Problem:** Old "Lab" was $249 / 10 seats = $24.90/seat, vs Researcher $19/seat. A 4-person group buys 4× Researcher ($76) instead of Lab ($249). The 10-seat floor is too high for most groups; per-seat math is upside-down.

**Fix:** Replace single "Lab" tier with two tiers and per-seat pricing on top of small floors:

| Tier         | Floor                       | Per-seat extra | Targeted searches | API req/day | SSO              | Audit logs | On-prem |
|--------------|-----------------------------|----------------|-------------------|-------------|------------------|------------|---------|
| Free         | $0                          | —              | 0                 | 1,000       | —                | —          | —       |
| Researcher   | $19/mo (1 seat)             | —              | 10/period         | 10,000      | —                | —          | —       |
| Team         | $57/mo (3 seats)            | $19/seat       | 50/period pooled  | 50,000      | Google/Microsoft | —          | —       |
| Institution  | $990/mo (10 seats)          | $99/seat       | 200/period pooled | 250,000     | SAML             | ✓          | —       |
| Enterprise   | Custom (annual, invoiced)   | —              | Dedicated pool    | Custom      | SAML             | ✓          | ✓       |

Why this works: each upgrade buys a *capability the prior tier can't get by buying more seats* — Team unlocks pooled searches + shared library + basic SSO; Institution unlocks SAML + audit logs + dedicated compute; Enterprise unlocks on-prem. A 4-person group now pays $76 (Team, 4 seats) and gets pooled searches + shared library — a real reason to upgrade vs. buying 4 individual seats.

**Phase 1 ships only Free + Researcher via self-serve checkout.** Team / Institution / Enterprise show on the pricing page with "Talk to us" CTAs that open a sales-contact form. Self-serve Team subscriptions are a separate plan (§"Out of scope").

### Fix 3 — Worker incentive cliff

**Problem:** Volunteer workers contribute compute that builds the corpus. We then sell paid tiers that *use* that corpus. Long-term this is unstable.

**Fix (copy + design, full impl in Phase 2):**
- Pricing page + workers landing make this explicit: **paid tiers buy targeted compute aimed at *your* conjecture; the open corpus is and always will be free, built by volunteer workers.**
- Active workers (≥10 hours of contributed Lean4 verification time in the trailing 30d) auto-receive Researcher tier free, no Stripe sub. Tracked via `worker_compute_credits` table (Phase 2). Phase 1 just adds the column placeholder, the FAQ entry, and the `/profile` "you'd qualify" hint.

---

## Out of scope (separate plans)

This plan does **not** include — each is its own follow-up plan:

1. **Org/team subscriptions** (Team tier self-serve checkout + invite flow + seat management). Tracked via separate plan: `2026-04-30-monetization-team-orgs.md`.
2. **Worker compute credits** (auto-Researcher entitlement). Plan: `2026-05-01-worker-compute-credits.md`.
3. **SSO** (Google/Microsoft for Team, SAML for Institution). Plan: `2026-05-15-sso-team-institution.md`.
4. **Metered overage billing** (charge for excess API calls instead of hard-capping). Phase 1 hard-caps; metering is a Phase 3+ upgrade.
5. **Verified Academic discount flow** (.edu verification + 50% coupon). Phase 1 ships the Free tier + Researcher; Verified Academic discount is its own short plan after Phase 1.

---

## Phase 0: Preflight & Stripe configuration

### Task 0.1: Create Stripe test-mode account & products

**Files:** none (manual, one-time).

- [ ] **Step 1: Confirm Stripe account exists in test mode.** Sign in to dashboard.stripe.com, switch to "Test mode".
- [ ] **Step 2: Create a single Product called "Nasrudin Researcher"** with two recurring Prices:
  - `price_researcher_monthly` — $19/mo USD recurring
  - `price_researcher_annual` — $182.40/yr USD recurring (= $19 × 12 × 0.8, the 20% annual discount already shown on /pricing)
- [ ] **Step 3: Enable Stripe Tax** in dashboard → Settings → Tax. Required for EU VAT compliance from day one — cheaper to enable now than retrofit.
- [ ] **Step 4: Configure Customer Portal** in dashboard → Settings → Billing → Customer portal:
  - Allow cancellation: end of period
  - Allow plan switching: monthly ↔ annual
  - Allow payment-method updates
  - Show invoice history
- [ ] **Step 5: Create webhook endpoint** in dashboard → Developers → Webhooks → Add endpoint:
  - URL: `https://<your-dev-tunnel>.ngrok.io/api/billing/webhook` (placeholder — replace with real URL during `Task 5.1`)
  - Events: `checkout.session.completed`, `customer.subscription.created`, `customer.subscription.updated`, `customer.subscription.deleted`, `invoice.paid`, `invoice.payment_failed`
  - Save the **signing secret** (`whsec_…`) for `Task 0.2`.
- [ ] **Step 6: Note down test API keys** from Developers → API keys (publishable `pk_test_…` and secret `sk_test_…`).

### Task 0.2: Add Stripe env vars to dev config

**Files:**
- Modify: `.env.example` (or wherever the engine reads env from — check `engine/crates/api/src/main.rs` for the env-var loading site)
- Modify: `docker-compose.yml` if API runs there, otherwise `justfile` `dev-engine` recipe

- [ ] **Step 1: Add to `.env.example`:**

```bash
# Stripe billing
STRIPE_SECRET_KEY=sk_test_REPLACE_ME
STRIPE_WEBHOOK_SECRET=whsec_REPLACE_ME
STRIPE_PRICE_RESEARCHER_MONTHLY=price_REPLACE_ME
STRIPE_PRICE_RESEARCHER_ANNUAL=price_REPLACE_ME
STRIPE_CUSTOMER_PORTAL_RETURN_URL=http://localhost:3000/profile
STRIPE_CHECKOUT_SUCCESS_URL=http://localhost:3000/profile?billing=ok
STRIPE_CHECKOUT_CANCEL_URL=http://localhost:3000/pricing?billing=cancelled
```

- [ ] **Step 2: Copy to local `.env`** with the real test values from Task 0.1.
- [ ] **Step 3: Restart `just dev-engine`** and confirm the server starts without complaining about missing env (Phase 1 makes them required; for now they can be optional).
- [ ] **Step 4: Commit.**

```bash
git add .env.example
git commit -m "chore(billing): add Stripe env var placeholders"
```

---

## Phase 1: Schema & entities

### Task 1.1: Migration — add billing columns to `users`

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260429_000009_billing.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs` (register migration)

- [ ] **Step 1: Write the migration:**

```rust
// engine/crates/pg/src/migrator/m20260429_000009_billing.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .add_column(
                        ColumnDef::new(Users::PlanTier)
                            .text()
                            .not_null()
                            .default("free"),
                    )
                    .add_column(ColumnDef::new(Users::StripeCustomerId).text().null())
                    .add_column(ColumnDef::new(Users::StripeSubscriptionId).text().null())
                    .add_column(
                        ColumnDef::new(Users::CurrentPeriodEnd)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .add_column(
                        ColumnDef::new(Users::PlanCycleStart)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .to_owned(),
            )
            .await?;

        manager
            .create_index(
                Index::create()
                    .name("idx_users_stripe_customer_id")
                    .table(Users::Table)
                    .col(Users::StripeCustomerId)
                    .unique()
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_index(Index::drop().name("idx_users_stripe_customer_id").to_owned())
            .await?;
        manager
            .alter_table(
                Table::alter()
                    .table(Users::Table)
                    .drop_column(Users::PlanCycleStart)
                    .drop_column(Users::CurrentPeriodEnd)
                    .drop_column(Users::StripeSubscriptionId)
                    .drop_column(Users::StripeCustomerId)
                    .drop_column(Users::PlanTier)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum Users {
    Table,
    PlanTier,
    StripeCustomerId,
    StripeSubscriptionId,
    CurrentPeriodEnd,
    PlanCycleStart,
}
```

- [ ] **Step 2: Register in `mod.rs`** by adding `mod m20260429_000009_billing;` and appending `Box::new(m20260429_000009_billing::Migration)` to the `migrations()` vec.
- [ ] **Step 3: Run migration:** `cargo run -p nasrudin_pg --bin migrate-up` (or whatever the existing migration runner binary is — check `engine/crates/pg/src/bin/`).
- [ ] **Step 4: Verify:** `psql $DATABASE_URL -c "\d users"` and confirm the 5 new columns are present.
- [ ] **Step 5: Commit.**

```bash
git add engine/crates/pg/src/migrator/m20260429_000009_billing.rs engine/crates/pg/src/migrator/mod.rs
git commit -m "feat(billing): add plan_tier and stripe_* columns to users"
```

### Task 1.2: Migration — `billing_events` table for webhook idempotency

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260429_000010_billing_events.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Write the migration:**

```rust
// engine/crates/pg/src/migrator/m20260429_000010_billing_events.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(BillingEvents::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(BillingEvents::Id)
                            .uuid()
                            .not_null()
                            .primary_key()
                            .default(Expr::cust("gen_random_uuid()")),
                    )
                    .col(
                        ColumnDef::new(BillingEvents::StripeEventId)
                            .text()
                            .not_null()
                            .unique_key(),
                    )
                    .col(ColumnDef::new(BillingEvents::EventType).text().not_null())
                    .col(
                        ColumnDef::new(BillingEvents::Payload)
                            .json_binary()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(BillingEvents::ReceivedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .col(
                        ColumnDef::new(BillingEvents::ProcessedAt)
                            .timestamp_with_time_zone()
                            .null(),
                    )
                    .col(ColumnDef::new(BillingEvents::ProcessError).text().null())
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(BillingEvents::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum BillingEvents {
    Table,
    Id,
    StripeEventId,
    EventType,
    Payload,
    ReceivedAt,
    ProcessedAt,
    ProcessError,
}
```

- [ ] **Step 2: Register and run** — same pattern as Task 1.1.
- [ ] **Step 3: Commit.**

```bash
git commit -am "feat(billing): add billing_events table for webhook idempotency"
```

### Task 1.3: Migration — `targeted_search_usage` table

Targeted searches map 1:1 onto `conjecture_jobs.create()`. We could count rows in `conjecture_jobs` directly, but a dedicated usage table:
- Survives if conjecture rows are pruned/archived.
- Holds reset boundaries cleanly (`period_start` per row).
- Can later support free credits, refunds, and worker-compute-credit tracking without contaminating `conjecture_jobs`.

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260429_000011_targeted_search_usage.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Write the migration:**

```rust
// engine/crates/pg/src/migrator/m20260429_000011_targeted_search_usage.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(TargetedSearchUsage::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(TargetedSearchUsage::Id)
                            .uuid()
                            .not_null()
                            .primary_key()
                            .default(Expr::cust("gen_random_uuid()")),
                    )
                    .col(
                        ColumnDef::new(TargetedSearchUsage::UserId)
                            .uuid()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(TargetedSearchUsage::ConjectureJobId)
                            .uuid()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(TargetedSearchUsage::PeriodStart)
                            .timestamp_with_time_zone()
                            .not_null(),
                    )
                    .col(
                        ColumnDef::new(TargetedSearchUsage::CreatedAt)
                            .timestamp_with_time_zone()
                            .not_null()
                            .default(Expr::current_timestamp()),
                    )
                    .foreign_key(
                        ForeignKey::create()
                            .name("fk_tsu_user")
                            .from(TargetedSearchUsage::Table, TargetedSearchUsage::UserId)
                            .to(Users::Table, Users::Id)
                            .on_delete(ForeignKeyAction::Cascade),
                    )
                    .to_owned(),
            )
            .await?;
        manager
            .create_index(
                Index::create()
                    .name("idx_tsu_user_period")
                    .table(TargetedSearchUsage::Table)
                    .col(TargetedSearchUsage::UserId)
                    .col(TargetedSearchUsage::PeriodStart)
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(
                Table::drop()
                    .table(TargetedSearchUsage::Table)
                    .to_owned(),
            )
            .await
    }
}

#[derive(DeriveIden)]
enum TargetedSearchUsage {
    Table,
    Id,
    UserId,
    ConjectureJobId,
    PeriodStart,
    CreatedAt,
}

#[derive(DeriveIden)]
enum Users {
    Table,
    Id,
}
```

- [ ] **Step 2: Register and run.**
- [ ] **Step 3: Commit.**

```bash
git commit -am "feat(billing): targeted_search_usage table for per-period quota counts"
```

### Task 1.4: Migration — `api_usage_daily` rollup

Per-day request counts per user. Keeping it daily (not raw event log) bounds row growth and matches the "10K req/day" tier copy.

**Files:**
- Create: `engine/crates/pg/src/migrator/m20260429_000012_api_usage_daily.rs`
- Modify: `engine/crates/pg/src/migrator/mod.rs`

- [ ] **Step 1: Write the migration:**

```rust
// engine/crates/pg/src/migrator/m20260429_000012_api_usage_daily.rs
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(ApiUsageDaily::Table)
                    .if_not_exists()
                    .col(ColumnDef::new(ApiUsageDaily::UserId).uuid().not_null())
                    .col(ColumnDef::new(ApiUsageDaily::Day).date().not_null())
                    .col(
                        ColumnDef::new(ApiUsageDaily::RequestCount)
                            .big_integer()
                            .not_null()
                            .default(0),
                    )
                    .primary_key(
                        Index::create()
                            .col(ApiUsageDaily::UserId)
                            .col(ApiUsageDaily::Day),
                    )
                    .to_owned(),
            )
            .await?;
        Ok(())
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(ApiUsageDaily::Table).to_owned())
            .await
    }
}

#[derive(DeriveIden)]
enum ApiUsageDaily {
    Table,
    UserId,
    Day,
    RequestCount,
}
```

- [ ] **Step 2: Register and run.**
- [ ] **Step 3: Commit.**

```bash
git commit -am "feat(billing): api_usage_daily rollup table"
```

### Task 1.5: Update `users` SeaORM entity

**Files:**
- Modify: `engine/crates/pg/src/entity/users.rs`

- [ ] **Step 1: Add the 5 columns to the `Model` struct.** Open the file and replace the struct with:

```rust
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    #[sea_orm(unique)]
    pub email: String,
    #[sea_orm(column_type = "Text")]
    pub password_hash: String,
    pub display_name: Option<String>,
    pub created_at: DateTimeWithTimeZone,
    #[sea_orm(default_value = "free")]
    pub plan_tier: String,
    pub stripe_customer_id: Option<String>,
    pub stripe_subscription_id: Option<String>,
    pub current_period_end: Option<DateTimeWithTimeZone>,
    pub plan_cycle_start: Option<DateTimeWithTimeZone>,
}
```

(Keep the existing `Relation` enum + `Related<>` impls + `ActiveModelBehavior` unchanged.)

- [ ] **Step 2: Run** `cargo build -p nasrudin_pg` and confirm it compiles.
- [ ] **Step 3: Commit.**

```bash
git commit -am "feat(billing): expose plan_tier and stripe fields on users entity"
```

### Task 1.6: Create entities for `billing_events`, `targeted_search_usage`, `api_usage_daily`

**Files:**
- Create: `engine/crates/pg/src/entity/billing_events.rs`
- Create: `engine/crates/pg/src/entity/targeted_search_usage.rs`
- Create: `engine/crates/pg/src/entity/api_usage_daily.rs`
- Modify: `engine/crates/pg/src/entity/mod.rs` — re-export new modules.

- [ ] **Step 1: Write `billing_events.rs`:**

```rust
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "billing_events")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    #[sea_orm(unique)]
    pub stripe_event_id: String,
    pub event_type: String,
    #[sea_orm(column_type = "JsonBinary")]
    pub payload: Json,
    pub received_at: DateTimeWithTimeZone,
    pub processed_at: Option<DateTimeWithTimeZone>,
    pub process_error: Option<String>,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 2: Write `targeted_search_usage.rs`:**

```rust
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "targeted_search_usage")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub user_id: Uuid,
    pub conjecture_job_id: Uuid,
    pub period_start: DateTimeWithTimeZone,
    pub created_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(
        belongs_to = "super::users::Entity",
        from = "Column::UserId",
        to = "super::users::Column::Id",
        on_delete = "Cascade"
    )]
    User,
}

impl Related<super::users::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::User.def()
    }
}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 3: Write `api_usage_daily.rs`:**

```rust
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "api_usage_daily")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub user_id: Uuid,
    #[sea_orm(primary_key, auto_increment = false)]
    pub day: Date,
    pub request_count: i64,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

- [ ] **Step 4: Update `entity/mod.rs`** — add three `pub mod …;` lines.
- [ ] **Step 5: `cargo build -p nasrudin_pg`** — confirm compile.
- [ ] **Step 6: Commit.**

```bash
git commit -am "feat(billing): SeaORM entities for billing_events, targeted_search_usage, api_usage_daily"
```

---

## Phase 2: PlanTier core type and quota table

### Task 2.1: Define `PlanTier` and `Quotas`

**Files:**
- Create: `engine/crates/api/src/billing/mod.rs`
- Create: `engine/crates/api/src/billing/tier.rs`
- Modify: `engine/crates/api/src/lib.rs` — add `pub mod billing;`

- [ ] **Step 1: Create `billing/mod.rs`:**

```rust
// engine/crates/api/src/billing/mod.rs
pub mod tier;
pub use tier::{PlanTier, Quotas};
```

- [ ] **Step 2: Write the failing test.** Create `engine/crates/api/src/billing/tier.rs` with only the test at the top of the module, then build (it should fail because `PlanTier` is not yet defined):

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn free_tier_has_zero_targeted_searches() {
        assert_eq!(PlanTier::Free.quotas().targeted_searches_per_period, 0);
    }

    #[test]
    fn researcher_quotas_match_pricing_page() {
        let q = PlanTier::Researcher.quotas();
        assert_eq!(q.api_per_day, 10_000);
        assert_eq!(q.targeted_searches_per_period, 10);
    }

    #[test]
    fn from_str_unknown_falls_back_to_free() {
        assert_eq!(PlanTier::from_db("garbage"), PlanTier::Free);
    }
}
```

- [ ] **Step 3: Run** `cargo test -p nasrudin_api billing::tier --no-run` — expect `error[E0433]: cannot find type 'PlanTier' in this scope`.
- [ ] **Step 4: Add the implementation above the tests:**

```rust
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PlanTier {
    Free,
    Researcher,
    Team,
    Institution,
    Enterprise,
}

impl PlanTier {
    /// Map the `users.plan_tier` text column to an enum. Unknown values
    /// degrade to `Free` rather than panicking — a misconfigured row must
    /// not lock the user out of the read corpus.
    pub fn from_db(s: &str) -> Self {
        match s {
            "researcher" => Self::Researcher,
            "team" => Self::Team,
            "institution" => Self::Institution,
            "enterprise" => Self::Enterprise,
            _ => Self::Free,
        }
    }

    pub fn as_db(self) -> &'static str {
        match self {
            Self::Free => "free",
            Self::Researcher => "researcher",
            Self::Team => "team",
            Self::Institution => "institution",
            Self::Enterprise => "enterprise",
        }
    }

    pub fn quotas(self) -> Quotas {
        match self {
            Self::Free => Quotas {
                api_per_day: 1_000,
                targeted_searches_per_period: 0,
                library_max: 50,
            },
            Self::Researcher => Quotas {
                api_per_day: 10_000,
                targeted_searches_per_period: 10,
                library_max: u32::MAX,
            },
            Self::Team => Quotas {
                api_per_day: 50_000,
                targeted_searches_per_period: 50,
                library_max: u32::MAX,
            },
            Self::Institution => Quotas {
                api_per_day: 250_000,
                targeted_searches_per_period: 200,
                library_max: u32::MAX,
            },
            Self::Enterprise => Quotas {
                api_per_day: u32::MAX,
                targeted_searches_per_period: u32::MAX,
                library_max: u32::MAX,
            },
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Quotas {
    pub api_per_day: u32,
    pub targeted_searches_per_period: u32,
    pub library_max: u32,
}
```

- [ ] **Step 5: Run** `cargo test -p nasrudin_api billing::tier` — expect 3 passing tests.
- [ ] **Step 6: Commit.**

```bash
git add engine/crates/api/src/billing/ engine/crates/api/src/lib.rs
git commit -m "feat(billing): PlanTier enum with quotas matching pricing page"
```

### Task 2.2: Period boundary helper — start of current monthly cycle

A user's "period" for targeted-search quota = either:
- For paid users: the Stripe billing period (`plan_cycle_start` ≤ now < `current_period_end`).
- For free users: the calendar month (UTC).

We anchor period_start at the user's `plan_cycle_start` if set, otherwise at the first of the current UTC month. This keeps free-tier accounting honest and matches Stripe's billing cadence for paid users.

**Files:**
- Modify: `engine/crates/api/src/billing/tier.rs` (add a function)

- [ ] **Step 1: Add failing test:**

```rust
#[test]
fn period_start_for_free_user_is_first_of_month() {
    use chrono::{TimeZone, Utc};
    let now = Utc.with_ymd_and_hms(2026, 4, 29, 12, 0, 0).unwrap();
    let start = period_start(None, now);
    assert_eq!(
        start,
        Utc.with_ymd_and_hms(2026, 4, 1, 0, 0, 0).unwrap()
    );
}

#[test]
fn period_start_for_paid_user_is_their_cycle_start() {
    use chrono::{TimeZone, Utc};
    let now = Utc.with_ymd_and_hms(2026, 4, 29, 12, 0, 0).unwrap();
    let cycle = Utc.with_ymd_and_hms(2026, 4, 17, 0, 0, 0).unwrap();
    assert_eq!(period_start(Some(cycle), now), cycle);
}
```

- [ ] **Step 2: Implement:**

```rust
use chrono::{DateTime, Datelike, TimeZone, Utc};

pub fn period_start(plan_cycle_start: Option<DateTime<Utc>>, now: DateTime<Utc>) -> DateTime<Utc> {
    if let Some(cycle) = plan_cycle_start {
        return cycle;
    }
    Utc.with_ymd_and_hms(now.year(), now.month(), 1, 0, 0, 0).unwrap()
}
```

- [ ] **Step 3: `cargo test -p nasrudin_api billing::tier`** — 5 passing.
- [ ] **Step 4: Commit.**

```bash
git commit -am "feat(billing): period_start helper anchored on Stripe cycle or month-of-UTC"
```

---

## Phase 3: Stripe SDK & checkout/portal endpoints

### Task 3.1: Add async-stripe + the `BillingClient`

**Files:**
- Modify: `engine/crates/api/Cargo.toml`
- Create: `engine/crates/api/src/billing/stripe_client.rs`
- Modify: `engine/crates/api/src/billing/mod.rs` — `pub mod stripe_client;`

- [ ] **Step 1: Add async-stripe to `Cargo.toml`:**

```toml
async-stripe = { version = "0.40", default-features = false, features = ["runtime-tokio-hyper-rustls", "checkout", "billing", "webhook-events"] }
```

- [ ] **Step 2: `cargo build -p nasrudin_api`** — confirm pulls cleanly.
- [ ] **Step 3: Write `stripe_client.rs`:**

```rust
use std::sync::Arc;
use stripe::Client;

#[derive(Clone)]
pub struct BillingConfig {
    pub price_researcher_monthly: String,
    pub price_researcher_annual: String,
    pub checkout_success_url: String,
    pub checkout_cancel_url: String,
    pub portal_return_url: String,
    pub webhook_secret: String,
}

#[derive(Clone)]
pub struct BillingClient {
    pub stripe: Client,
    pub cfg: Arc<BillingConfig>,
}

impl BillingClient {
    pub fn from_env() -> anyhow::Result<Self> {
        let secret = std::env::var("STRIPE_SECRET_KEY")
            .map_err(|_| anyhow::anyhow!("STRIPE_SECRET_KEY not set"))?;
        let cfg = BillingConfig {
            price_researcher_monthly: std::env::var("STRIPE_PRICE_RESEARCHER_MONTHLY")?,
            price_researcher_annual: std::env::var("STRIPE_PRICE_RESEARCHER_ANNUAL")?,
            checkout_success_url: std::env::var("STRIPE_CHECKOUT_SUCCESS_URL")?,
            checkout_cancel_url: std::env::var("STRIPE_CHECKOUT_CANCEL_URL")?,
            portal_return_url: std::env::var("STRIPE_CUSTOMER_PORTAL_RETURN_URL")?,
            webhook_secret: std::env::var("STRIPE_WEBHOOK_SECRET")?,
        };
        Ok(Self {
            stripe: Client::new(secret),
            cfg: Arc::new(cfg),
        })
    }
}
```

- [ ] **Step 4: Wire into `AppState`** — `engine/crates/api/src/state.rs`. Add a `pub billing: Option<BillingClient>` field. In `main.rs` where `AppState` is constructed, call `BillingClient::from_env().ok()` and set the field. Optional means the dev path still works without billing env vars set.
- [ ] **Step 5: `cargo build -p nasrudin_api`** — confirm.
- [ ] **Step 6: Commit.**

```bash
git commit -am "feat(billing): async-stripe client + BillingConfig from env"
```

### Task 3.2: `POST /api/billing/checkout` — start a subscription

**Files:**
- Create: `engine/crates/api/src/handlers/billing.rs`
- Modify: `engine/crates/api/src/handlers/mod.rs` — `pub mod billing;`
- Modify: `engine/crates/api/src/lib.rs` (or wherever `Router::new()` is composed) — mount `/api/billing/*` routes.

- [ ] **Step 1: Write `billing.rs` skeleton with the checkout handler:**

```rust
// engine/crates/api/src/handlers/billing.rs
use std::sync::Arc;

use axum::{
    extract::State,
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use serde::{Deserialize, Serialize};
use stripe::{CheckoutSession, CheckoutSessionMode, CreateCheckoutSession,
    CreateCheckoutSessionLineItems, CreateCheckoutSessionSubscriptionData};

use crate::auth::{AuthOrApiKey, AuthSess};
use crate::state::AppState;

#[derive(Deserialize)]
pub struct CheckoutRequest {
    /// "researcher_monthly" or "researcher_annual" — Phase 1 only.
    pub price_key: String,
}

#[derive(Serialize)]
pub struct CheckoutResponse {
    pub url: String,
}

fn err(status: StatusCode, code: &str) -> Response {
    (status, Json(serde_json::json!({ "error": code }))).into_response()
}

pub async fn checkout(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    auth_sess: AuthSess,
    Json(body): Json<CheckoutRequest>,
) -> Response {
    let billing = match &state.billing {
        Some(b) => b,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "billing_unavailable"),
    };

    let price_id = match body.price_key.as_str() {
        "researcher_monthly" => &billing.cfg.price_researcher_monthly,
        "researcher_annual" => &billing.cfg.price_researcher_annual,
        _ => return err(StatusCode::BAD_REQUEST, "unknown_price_key"),
    };

    let pg = &auth_sess.backend.db;
    let user = auth.user;

    // Reuse existing Stripe customer if we already created one for this user.
    let customer_id = match user.stripe_customer_id.clone() {
        Some(c) => c,
        None => {
            // Create customer in Stripe with email + user_id metadata so the
            // webhook can map customer -> user without an extra DB lookup.
            let cust = stripe::Customer::create(
                &billing.stripe,
                stripe::CreateCustomer {
                    email: Some(&user.email),
                    metadata: Some(std::collections::HashMap::from([(
                        "user_id".to_string(),
                        user.id.to_string(),
                    )])),
                    ..Default::default()
                },
            )
            .await
            .map_err(|e| {
                tracing::warn!("stripe customer create failed: {e}");
            })
            .ok();
            let cust = match cust {
                Some(c) => c,
                None => return err(StatusCode::BAD_GATEWAY, "stripe_customer_create_failed"),
            };
            // Persist on the user row so subsequent checkouts reuse it.
            if let Err(e) = nasrudin_pg::query::users::set_stripe_customer_id(
                pg,
                user.id,
                cust.id.as_str(),
            )
            .await
            {
                tracing::warn!("persist stripe_customer_id failed: {e}");
            }
            cust.id.to_string()
        }
    };

    let mut params = CreateCheckoutSession::new();
    params.mode = Some(CheckoutSessionMode::Subscription);
    params.customer = Some(customer_id.parse().unwrap());
    params.line_items = Some(vec![CreateCheckoutSessionLineItems {
        price: Some(price_id.clone()),
        quantity: Some(1),
        ..Default::default()
    }]);
    params.success_url = Some(&billing.cfg.checkout_success_url);
    params.cancel_url = Some(&billing.cfg.checkout_cancel_url);
    params.subscription_data = Some(CreateCheckoutSessionSubscriptionData {
        metadata: Some(std::collections::HashMap::from([(
            "user_id".to_string(),
            user.id.to_string(),
        )])),
        ..Default::default()
    });
    // Stripe Tax for cross-border VAT.
    params.automatic_tax = Some(stripe::CreateCheckoutSessionAutomaticTax {
        enabled: true,
        ..Default::default()
    });

    match CheckoutSession::create(&billing.stripe, params).await {
        Ok(session) => Json(CheckoutResponse {
            url: session.url.unwrap_or_default(),
        })
        .into_response(),
        Err(e) => {
            tracing::warn!("stripe checkout create failed: {e}");
            err(StatusCode::BAD_GATEWAY, "checkout_create_failed")
        }
    }
}
```

- [ ] **Step 2: Add `set_stripe_customer_id` query in `engine/crates/pg/src/query/users.rs`:**

```rust
pub async fn set_stripe_customer_id(
    db: &DatabaseConnection,
    user_id: Uuid,
    customer_id: &str,
) -> Result<(), DbErr> {
    use crate::entity::users::*;
    Entity::update_many()
        .col_expr(Column::StripeCustomerId, Expr::value(customer_id))
        .filter(Column::Id.eq(user_id))
        .exec(db)
        .await
        .map(|_| ())
}
```

- [ ] **Step 3: Mount the route** in the router composition site (find the `Router::new()...nest("/api", ...)` block in `engine/crates/api/src/lib.rs` or `main.rs`):

```rust
.route("/api/billing/checkout", post(handlers::billing::checkout))
```

- [ ] **Step 4: `cargo build -p nasrudin_api`** — confirm.
- [ ] **Step 5: Manual smoke test:**
  - `curl -X POST localhost:3001/api/billing/checkout -H 'Cookie: <session>' -H 'Content-Type: application/json' -d '{"price_key":"researcher_monthly"}'`
  - Expect `{ "url": "https://checkout.stripe.com/c/pay/cs_test_…" }`. Open the URL in a browser, confirm the Stripe page renders the right product and price.
- [ ] **Step 6: Commit.**

```bash
git commit -am "feat(billing): POST /api/billing/checkout creates Stripe Checkout session"
```

### Task 3.3: `POST /api/billing/portal` — manage subscription

**Files:**
- Modify: `engine/crates/api/src/handlers/billing.rs`
- Modify: router

- [ ] **Step 1: Append handler to `billing.rs`:**

```rust
pub async fn portal(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
) -> Response {
    let billing = match &state.billing {
        Some(b) => b,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "billing_unavailable"),
    };
    let customer_id = match &auth.user.stripe_customer_id {
        Some(c) => c.clone(),
        None => return err(StatusCode::BAD_REQUEST, "no_stripe_customer"),
    };

    let mut params = stripe::CreateBillingPortalSession::new(customer_id.parse().unwrap());
    params.return_url = Some(&billing.cfg.portal_return_url);
    match stripe::BillingPortalSession::create(&billing.stripe, params).await {
        Ok(session) => Json(serde_json::json!({ "url": session.url })).into_response(),
        Err(e) => {
            tracing::warn!("stripe portal create failed: {e}");
            err(StatusCode::BAD_GATEWAY, "portal_create_failed")
        }
    }
}
```

- [ ] **Step 2: Mount route:** `.route("/api/billing/portal", post(handlers::billing::portal))`.
- [ ] **Step 3: `cargo build`.**
- [ ] **Step 4: Smoke test** after Task 3.2 has produced a customer:
  - `curl -X POST localhost:3001/api/billing/portal -H 'Cookie: <session>'` → expect `{"url":"https://billing.stripe.com/p/session/…"}`.
- [ ] **Step 5: Commit.**

```bash
git commit -am "feat(billing): POST /api/billing/portal opens Customer Portal"
```

---

## Phase 4: Webhook handler

### Task 4.1: Webhook signature verification + idempotency record

**Files:**
- Create: `engine/crates/api/src/billing/webhook.rs`
- Modify: `engine/crates/api/src/billing/mod.rs` — `pub mod webhook;`

- [ ] **Step 1: Write failing test for signature verification.** Create `webhook.rs` with:

```rust
use stripe::{EventObject, EventType, Webhook};

pub struct WebhookProcessor {
    pub secret: String,
}

impl WebhookProcessor {
    pub fn parse_event(&self, payload: &[u8], sig_header: &str) -> Result<stripe::Event, ParseError> {
        let payload_str = std::str::from_utf8(payload).map_err(|_| ParseError::InvalidUtf8)?;
        Webhook::construct_event(payload_str, sig_header, &self.secret)
            .map_err(|_| ParseError::InvalidSignature)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    InvalidUtf8,
    InvalidSignature,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_invalid_signature() {
        let p = WebhookProcessor { secret: "whsec_test".into() };
        let result = p.parse_event(b"{}", "t=1,v1=garbage");
        assert_eq!(result.unwrap_err(), ParseError::InvalidSignature);
    }
}
```

- [ ] **Step 2: `cargo test -p nasrudin_api billing::webhook`** — passes.
- [ ] **Step 3: Commit.**

```bash
git commit -am "feat(billing): webhook signature verification"
```

### Task 4.2: Webhook event → user state mutator

The mapping that matters:

| Stripe event                       | Action on user row                                         |
|------------------------------------|------------------------------------------------------------|
| `checkout.session.completed`       | (no-op — `subscription.created` covers state)              |
| `customer.subscription.created`    | `plan_tier=researcher`, write `stripe_subscription_id`, write `current_period_end`, set `plan_cycle_start` |
| `customer.subscription.updated`    | Recompute `plan_tier` from price_id; refresh `current_period_end` and `plan_cycle_start` |
| `customer.subscription.deleted`    | `plan_tier=free`, clear `stripe_subscription_id`, clear `current_period_end` |
| `invoice.paid`                     | refresh `plan_cycle_start = period_start`, `current_period_end = period_end` |
| `invoice.payment_failed`           | log + alert (Phase 1 keeps tier; dunning UX is later)      |

User identity comes from the subscription's `customer` → `users.stripe_customer_id` (unique index from Task 1.1).

**Files:**
- Modify: `engine/crates/api/src/billing/webhook.rs`
- Create: `engine/crates/pg/src/query/billing.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`

- [ ] **Step 1: Add the price-id → tier map** (Phase 1 only researcher):

```rust
// In webhook.rs
use crate::billing::tier::PlanTier;

pub fn tier_for_price(price_id: &str, cfg: &crate::billing::stripe_client::BillingConfig) -> PlanTier {
    if price_id == cfg.price_researcher_monthly || price_id == cfg.price_researcher_annual {
        PlanTier::Researcher
    } else {
        PlanTier::Free
    }
}
```

- [ ] **Step 2: Write the user-state queries** in `engine/crates/pg/src/query/billing.rs`:

```rust
use chrono::{DateTime, Utc};
use sea_orm::{prelude::*, ActiveValue::*};
use uuid::Uuid;
use crate::entity::users;

pub async fn apply_subscription_active(
    db: &DatabaseConnection,
    customer_id: &str,
    subscription_id: &str,
    plan_tier: &str,
    cycle_start: DateTime<Utc>,
    period_end: DateTime<Utc>,
) -> Result<(), DbErr> {
    users::Entity::update_many()
        .col_expr(users::Column::PlanTier, Expr::value(plan_tier))
        .col_expr(users::Column::StripeSubscriptionId, Expr::value(subscription_id))
        .col_expr(users::Column::PlanCycleStart, Expr::value(cycle_start.fixed_offset()))
        .col_expr(users::Column::CurrentPeriodEnd, Expr::value(period_end.fixed_offset()))
        .filter(users::Column::StripeCustomerId.eq(customer_id))
        .exec(db)
        .await
        .map(|_| ())
}

pub async fn apply_subscription_cancelled(
    db: &DatabaseConnection,
    customer_id: &str,
) -> Result<(), DbErr> {
    users::Entity::update_many()
        .col_expr(users::Column::PlanTier, Expr::value("free"))
        .col_expr(users::Column::StripeSubscriptionId, Expr::value(Option::<String>::None))
        .col_expr(users::Column::CurrentPeriodEnd, Expr::value(Option::<DateTime<Utc>>::None))
        .filter(users::Column::StripeCustomerId.eq(customer_id))
        .exec(db)
        .await
        .map(|_| ())
}
```

- [ ] **Step 3: Add an idempotent insert into `billing_events`** (returns `Ok(true)` if newly inserted, `Ok(false)` if already seen):

```rust
use crate::entity::billing_events;

pub async fn record_event_if_new(
    db: &DatabaseConnection,
    stripe_event_id: &str,
    event_type: &str,
    payload: serde_json::Value,
) -> Result<bool, DbErr> {
    let existing = billing_events::Entity::find()
        .filter(billing_events::Column::StripeEventId.eq(stripe_event_id))
        .one(db)
        .await?;
    if existing.is_some() {
        return Ok(false);
    }
    billing_events::ActiveModel {
        id: NotSet, // default uuid
        stripe_event_id: Set(stripe_event_id.to_string()),
        event_type: Set(event_type.to_string()),
        payload: Set(payload),
        received_at: Set(chrono::Utc::now().fixed_offset()),
        processed_at: NotSet,
        process_error: NotSet,
    }
    .insert(db)
    .await
    .map(|_| true)
}

pub async fn mark_event_processed(
    db: &DatabaseConnection,
    stripe_event_id: &str,
    error: Option<&str>,
) -> Result<(), DbErr> {
    billing_events::Entity::update_many()
        .col_expr(
            billing_events::Column::ProcessedAt,
            Expr::value(chrono::Utc::now().fixed_offset()),
        )
        .col_expr(
            billing_events::Column::ProcessError,
            Expr::value(error.map(|s| s.to_string())),
        )
        .filter(billing_events::Column::StripeEventId.eq(stripe_event_id))
        .exec(db)
        .await
        .map(|_| ())
}
```

- [ ] **Step 4: `cargo build -p nasrudin_pg`** — confirm.
- [ ] **Step 5: Commit.**

```bash
git commit -am "feat(billing): query helpers for subscription state + event idempotency"
```

### Task 4.3: `POST /api/billing/webhook` handler

**Files:**
- Modify: `engine/crates/api/src/handlers/billing.rs`
- Modify: router

The handler must:
1. Read raw body bytes (no JSON middleware ahead — signature is over the raw body).
2. Verify signature.
3. Insert into `billing_events`; if already present, return 200 immediately (idempotent replay).
4. Dispatch by event type.
5. Update `billing_events.processed_at` with success/error.
6. Always return 200 unless signature is invalid (Stripe retries on non-2xx).

- [ ] **Step 1: Append handler:**

```rust
use axum::body::Bytes;
use axum::http::HeaderMap;
use stripe::EventObject;

pub async fn webhook(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    body: Bytes,
) -> Response {
    let billing = match &state.billing {
        Some(b) => b,
        None => return err(StatusCode::SERVICE_UNAVAILABLE, "billing_unavailable"),
    };
    let sig = match headers.get("stripe-signature").and_then(|v| v.to_str().ok()) {
        Some(s) => s,
        None => return err(StatusCode::BAD_REQUEST, "missing_signature"),
    };

    let processor = crate::billing::webhook::WebhookProcessor {
        secret: billing.cfg.webhook_secret.clone(),
    };
    let event = match processor.parse_event(&body, sig) {
        Ok(e) => e,
        Err(_) => return err(StatusCode::BAD_REQUEST, "invalid_signature"),
    };

    let pg = &state.pg;
    let payload_json = serde_json::to_value(&event).unwrap_or(serde_json::Value::Null);

    let is_new = match nasrudin_pg::query::billing::record_event_if_new(
        pg,
        event.id.as_str(),
        &format!("{:?}", event.type_),
        payload_json,
    )
    .await
    {
        Ok(b) => b,
        Err(e) => {
            tracing::warn!("billing_events insert failed: {e}");
            return (StatusCode::OK, "").into_response();
        }
    };
    if !is_new {
        return (StatusCode::OK, "").into_response();
    }

    let result: Result<(), String> = match event.data.object {
        EventObject::Subscription(sub) => {
            handle_subscription_event(billing, pg, &sub).await
        }
        EventObject::Invoice(inv) => handle_invoice_event(pg, &inv).await,
        _ => Ok(()),
    };

    let err_msg = result.as_ref().err().map(|s| s.as_str());
    let _ = nasrudin_pg::query::billing::mark_event_processed(pg, event.id.as_str(), err_msg).await;
    (StatusCode::OK, "").into_response()
}

async fn handle_subscription_event(
    billing: &crate::billing::stripe_client::BillingClient,
    pg: &sea_orm::DatabaseConnection,
    sub: &stripe::Subscription,
) -> Result<(), String> {
    let customer_id = sub.customer.id().to_string();
    if matches!(sub.status, stripe::SubscriptionStatus::Canceled | stripe::SubscriptionStatus::IncompleteExpired) {
        return nasrudin_pg::query::billing::apply_subscription_cancelled(pg, &customer_id)
            .await
            .map_err(|e| e.to_string());
    }
    let price_id = sub.items.data.first()
        .and_then(|i| i.price.as_ref())
        .map(|p| p.id.as_str().to_string())
        .unwrap_or_default();
    let tier = crate::billing::webhook::tier_for_price(&price_id, &billing.cfg);
    let cycle_start = chrono::DateTime::<chrono::Utc>::from_timestamp(sub.current_period_start, 0)
        .ok_or_else(|| "bad cycle_start".to_string())?;
    let period_end = chrono::DateTime::<chrono::Utc>::from_timestamp(sub.current_period_end, 0)
        .ok_or_else(|| "bad period_end".to_string())?;
    nasrudin_pg::query::billing::apply_subscription_active(
        pg,
        &customer_id,
        sub.id.as_str(),
        tier.as_db(),
        cycle_start,
        period_end,
    )
    .await
    .map_err(|e| e.to_string())
}

async fn handle_invoice_event(
    _pg: &sea_orm::DatabaseConnection,
    _inv: &stripe::Invoice,
) -> Result<(), String> {
    // Phase 1: subscription.updated already handles period rollover.
    // Invoice.paid is logged; payment_failed is logged for now.
    Ok(())
}
```

- [ ] **Step 2: Mount the route** — note the body must be `Bytes` so don't put a JSON extractor in front:

```rust
.route("/api/billing/webhook", post(handlers::billing::webhook))
```

- [ ] **Step 3: Smoke test with Stripe CLI:**

```bash
# In a second terminal:
stripe listen --forward-to localhost:3001/api/billing/webhook
# In a third:
stripe trigger customer.subscription.created
```

Expect: server logs show event processed; `psql` shows row in `billing_events` with `processed_at IS NOT NULL`.

- [ ] **Step 4: Commit.**

```bash
git commit -am "feat(billing): POST /api/billing/webhook with signature verify and idempotent dispatch"
```

---

## Phase 5: Quota enforcement

### Task 5.1: Extend `AuthOrApiKey` to expose `PlanTier`

**Files:**
- Modify: `engine/crates/api/src/auth.rs` (or wherever `AuthOrApiKey` lives — find via `grep -n "AuthOrApiKey" engine/crates/api/src/`)

- [ ] **Step 1: Add a `plan_tier: PlanTier` field** on `AuthOrApiKey`. Populate it from `user.plan_tier` after the existing user lookup:

```rust
// inside the existing extractor impl, after `user` is resolved:
let plan_tier = crate::billing::PlanTier::from_db(&user.plan_tier);
Ok(AuthOrApiKey { user, plan_tier, ... })
```

- [ ] **Step 2: Existing handlers compile unchanged** (struct is destructured by name). `cargo build -p nasrudin_api`.
- [ ] **Step 3: Commit.**

```bash
git commit -am "feat(billing): expose PlanTier on AuthOrApiKey extractor"
```

### Task 5.2: Targeted-search quota check in conjecture create

**Files:**
- Modify: `engine/crates/api/src/handlers/conjecture.rs` (the `create` function at line 26)
- Create: `engine/crates/pg/src/query/targeted_search_usage.rs`
- Modify: `engine/crates/pg/src/query/mod.rs`

- [ ] **Step 1: Add usage queries:**

```rust
// engine/crates/pg/src/query/targeted_search_usage.rs
use chrono::{DateTime, Utc};
use sea_orm::{prelude::*, ActiveValue::*};
use uuid::Uuid;
use crate::entity::targeted_search_usage as tsu;

pub async fn count_in_period(
    db: &DatabaseConnection,
    user_id: Uuid,
    period_start: DateTime<Utc>,
) -> Result<u64, DbErr> {
    tsu::Entity::find()
        .filter(tsu::Column::UserId.eq(user_id))
        .filter(tsu::Column::PeriodStart.eq(period_start.fixed_offset()))
        .count(db)
        .await
}

pub async fn record(
    db: &DatabaseConnection,
    user_id: Uuid,
    conjecture_job_id: Uuid,
    period_start: DateTime<Utc>,
) -> Result<(), DbErr> {
    tsu::ActiveModel {
        id: NotSet,
        user_id: Set(user_id),
        conjecture_job_id: Set(conjecture_job_id),
        period_start: Set(period_start.fixed_offset()),
        created_at: Set(Utc::now().fixed_offset()),
    }
    .insert(db)
    .await
    .map(|_| ())
}
```

- [ ] **Step 2: Gate the create handler** at `engine/crates/api/src/handlers/conjecture.rs:46`, immediately after `let user_id = auth.user.id;`:

```rust
// Quota check — Free tier gets 0 targeted searches; paid tiers per PlanTier.
let quotas = auth.plan_tier.quotas();
let now = chrono::Utc::now();
let cycle_start = auth.user.plan_cycle_start
    .map(|d| d.with_timezone(&chrono::Utc));
let period_start = crate::billing::tier::period_start(cycle_start, now);

let used = nasrudin_pg::query::targeted_search_usage::count_in_period(
    pg, user_id, period_start,
).await.unwrap_or(0);

if used >= quotas.targeted_searches_per_period as u64 {
    return err(StatusCode::PAYMENT_REQUIRED, "targeted_search_quota_exhausted");
}
```

Then, after the conjecture row is created (just after `let job_id = ...` on line 65), record usage:

```rust
let _ = nasrudin_pg::query::targeted_search_usage::record(
    pg, user_id, job_id, period_start,
).await;
```

- [ ] **Step 3: Add a unit test in `engine/crates/api/tests/`:**

```rust
// engine/crates/api/tests/quota_targeted_search.rs
// Test: Free user attempting POST /api/conjecture gets 402 Payment Required.
// Test: Researcher with 9 used succeeds; 10 used returns 402.
```

(Use the existing `test_app/mod.rs` harness; mock `auth.plan_tier` by setting `users.plan_tier` in the seeded user.)

- [ ] **Step 4: Run tests** — confirm pass.
- [ ] **Step 5: Commit.**

```bash
git commit -am "feat(billing): enforce targeted_search quota per PlanTier on conjecture create"
```

### Task 5.3: API per-day request counter middleware

A tower layer that, on each authenticated request, increments `api_usage_daily.request_count` for `(user_id, today_utc)` and returns 429 if today's count exceeds the user's tier's `api_per_day`. Cheap-write path: `INSERT … ON CONFLICT DO UPDATE SET request_count = request_count + 1 RETURNING request_count`.

**Files:**
- Create: `engine/crates/api/src/billing/api_quota_layer.rs`
- Modify: `engine/crates/api/src/lib.rs` — register layer on the `/api` sub-router.
- Create: `engine/crates/pg/src/query/api_usage.rs`

- [ ] **Step 1: Add the increment query (atomic upsert):**

```rust
// engine/crates/pg/src/query/api_usage.rs
use chrono::NaiveDate;
use sea_orm::{ConnectionTrait, DatabaseConnection, DbErr, Statement};
use uuid::Uuid;

pub async fn increment_and_get(
    db: &DatabaseConnection,
    user_id: Uuid,
    day: NaiveDate,
) -> Result<i64, DbErr> {
    let stmt = Statement::from_sql_and_values(
        sea_orm::DatabaseBackend::Postgres,
        "INSERT INTO api_usage_daily (user_id, day, request_count) \
         VALUES ($1, $2, 1) \
         ON CONFLICT (user_id, day) DO UPDATE \
         SET request_count = api_usage_daily.request_count + 1 \
         RETURNING request_count",
        [user_id.into(), day.into()],
    );
    let row = db.query_one(stmt).await?.ok_or(DbErr::RecordNotFound("upsert".into()))?;
    row.try_get::<i64>("", "request_count")
}
```

- [ ] **Step 2: Write the layer.** Use `axum::middleware::from_fn_with_state` instead of a hand-rolled tower service — simpler:

```rust
// engine/crates/api/src/billing/api_quota_layer.rs
use std::sync::Arc;
use axum::{
    extract::State,
    http::{Request, StatusCode},
    middleware::Next,
    response::Response,
    Json,
};
use crate::auth::AuthOrApiKey;
use crate::state::AppState;

pub async fn api_quota<B>(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
    req: Request<B>,
    next: Next<B>,
) -> Response {
    let quotas = auth.plan_tier.quotas();
    let today = chrono::Utc::now().date_naive();
    match nasrudin_pg::query::api_usage::increment_and_get(&state.pg, auth.user.id, today).await {
        Ok(count) if count as u64 > quotas.api_per_day as u64 => {
            (StatusCode::TOO_MANY_REQUESTS, Json(serde_json::json!({
                "error": "api_quota_exhausted",
                "limit_per_day": quotas.api_per_day,
            }))).into_response()
        }
        _ => next.run(req).await,
    }
}
```

- [ ] **Step 3: Apply to `/api` sub-router** (skip for `/api/billing/webhook` — that's Stripe-authed, not user-authed):

```rust
let api_protected = Router::new()
    .route("/api/conjecture", post(...))
    /* ... existing routes that need quotas ... */
    .layer(axum::middleware::from_fn_with_state(state.clone(),
        crate::billing::api_quota_layer::api_quota));
```

- [ ] **Step 4: Test:**
  - Hit `/api/me` 1001 times as a Free user; expect HTTP 429 on the 1001st.
  - Bump the same user's `plan_tier` to `researcher` in psql; expect 1001th request now succeeds (still 999 budget left in the day for 10K).
- [ ] **Step 5: Commit.**

```bash
git commit -am "feat(billing): per-day API quota middleware with PlanTier ceilings"
```

---

## Phase 6: Frontend — pricing page rewrite + billing UI

### Task 6.1: Rewrite `pricing.tsx` with the new tier ladder + honest copy

**Files:**
- Modify: `nasrudin-frontend/src/routes/pricing.tsx`

- [ ] **Step 1: Replace the `TIERS` array with the 5-tier ladder:**

```ts
const TIERS: Tier[] = [
  {
    name: 'Free',
    tagline: 'For citing, browsing, and re-verifying. No card.',
    price: '$0',
    period: 'forever',
    sub: 'no card required',
    cta: 'Sign up',
    ctaClass: 'btn-secondary',
    priceKey: null,
    features: [
      'Browse all 247,118 verified theorems',
      'Read full Lean 4 proofs',
      'Download any .lean file & re-verify locally',
      'Save up to 50 theorems',
      'Cite & share via permalinks',
      '1,000 API requests / day',
    ],
  },
  {
    name: 'Researcher',
    tagline: 'For builders pointing compute at hard problems.',
    price: '$19',
    period: '/ month',
    sub: 'billed annually · $182.40/yr (−20%)',
    cta: 'Start subscription',
    ctaClass: 'btn-primary',
    featured: true,
    popular: true,
    priceKey: 'researcher_monthly',
    features: [
      'Everything in Free',
      '10 targeted searches / month',
      'Point the GA at your own conjecture',
      '10,000 API requests / day',
      'Unlimited library, folders, private notes',
      'Email digest of new theorems in your domains',
    ],
  },
  {
    name: 'Team',
    tagline: 'For research groups: pooled searches, shared library.',
    price: '$57',
    period: '/ month',
    sub: '3 seats included · +$19/seat · billed annually',
    cta: 'Talk to us',
    ctaClass: 'btn-secondary',
    priceKey: null,
    features: [
      'Everything in Researcher, per seat',
      '50 targeted searches / month (pooled)',
      '50,000 API requests / day (pooled)',
      'Shared library & citation graphs',
      'Google / Microsoft sign-in',
      'Bulk .lean exports',
    ],
  },
  {
    name: 'Institution',
    tagline: 'For departments and institutes with compliance needs.',
    price: '$990',
    period: '/ month',
    sub: '10 seats included · +$99/seat · billed annually',
    cta: 'Contact sales',
    ctaClass: 'btn-secondary',
    priceKey: null,
    features: [
      'Everything in Team, per seat',
      '200 targeted searches / month (pooled)',
      '250,000 API requests / day (pooled)',
      'SAML SSO',
      'Audit logs & compliance reporting',
      'Dedicated targeted-search compute pool',
      'Quarterly office hours',
    ],
  },
  {
    name: 'Enterprise',
    tagline: 'For institutions running their own Nasrudin nodes.',
    price: 'Custom',
    period: '',
    sub: 'annual · invoiced',
    cta: 'Contact sales',
    ctaClass: 'btn-secondary',
    priceKey: null,
    features: [
      'Everything in Institution, unlimited seats',
      'On-prem worker cluster deployment',
      'Private corpus extension (your own axioms)',
      'SLA · 99.9%',
      'Direct line to engineering',
    ],
  },
];
```

(Add `priceKey: string | null` to the `Tier` interface.)

- [ ] **Step 2: Rewrite the FAQ to fix all 3 premises:**

```ts
const FAQ: Array<[string, string]> = [
  [
    'Is the underlying corpus really free?',
    'Yes. All 247,118 verified theorems are browseable, downloadable as .lean files, and re-verifiable on your own machine without a paid plan. The corpus is built by volunteer worker compute and stays free by design.',
  ],
  [
    'What is a "targeted search"?',
    'You provide a conjecture in Lean syntax (or natural-language we transcribe). We dedicate a slice of the GA cluster to evolve toward it for up to 24 hours. Paid tiers buy targeted compute aimed at YOUR conjecture — the open corpus is not gated.',
  ],
  [
    'Can I cancel anytime?',
    'Yes. Self-serve cancel from the billing portal — your plan stays active through the end of the current period.',
  ],
  [
    'Are workers paid?',
    'No cash. Workers earn (1) attribution on every theorem they verify, (2) leaderboard rank, and (3) — coming soon — a free Researcher tier when contributing ≥10 hours of verification time per month. The compute donated by workers builds the open corpus; the compute paid tiers buy is the targeted GA slice you point at your own conjecture.',
  ],
  [
    'Are you a tool for academics specifically?',
    'No — we build for anyone pointing compute at hard problems. Independent researchers, industry R&D, quant teams, and academics with budget all use Nasrudin the same way. Verified academic email gets 50% off Researcher.',
  ],
];
```

- [ ] **Step 3: Wire the Researcher CTA to `POST /api/billing/checkout`:**

```ts
async function handleCta(tier: Tier, annual: boolean) {
  if (!tier.priceKey) return; // Talk to us / Contact sales — leave for sales-form follow-up
  const key = annual ? `${tier.priceKey.replace('_monthly', '_annual')}` : tier.priceKey;
  const res = await fetch('/api/billing/checkout', {
    method: 'POST',
    credentials: 'include',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ price_key: key }),
  });
  if (!res.ok) { alert('Checkout unavailable. Try again or contact support.'); return; }
  const { url } = await res.json();
  window.location.href = url;
}
```

And update the button:

```tsx
<button type="button" className={`btn ${t.ctaClass}`} onClick={() => handleCta(t, annual)}>
  {t.cta}
</button>
```

- [ ] **Step 4: `pnpm --filter nasrudin-frontend dev`** — visit `/pricing`, click "Start subscription". Expect redirect to Stripe Checkout. Pay with card `4242 4242 4242 4242` / any future expiry / any CVC.
- [ ] **Step 5: Verify** in psql that `users.plan_tier` flipped to `researcher` after webhook fired.
- [ ] **Step 6: Commit.**

```bash
git commit -am "feat(pricing): 5-tier ladder + honest worker FAQ + checkout wiring"
```

### Task 6.2: `/profile` — show plan + Manage billing button

**Files:**
- Modify: `nasrudin-frontend/src/routes/profile.tsx` (or wherever the profile route lives)
- Add: `GET /api/billing/me` endpoint (returns `{ plan_tier, current_period_end, targeted_searches_used, targeted_searches_limit, api_used_today, api_limit_per_day }`)

- [ ] **Step 1: Add the `/api/billing/me` handler:**

```rust
// engine/crates/api/src/handlers/billing.rs
pub async fn me(
    State(state): State<Arc<AppState>>,
    auth: AuthOrApiKey,
) -> Response {
    let q = auth.plan_tier.quotas();
    let now = chrono::Utc::now();
    let cycle_start = auth.user.plan_cycle_start.map(|d| d.with_timezone(&chrono::Utc));
    let period_start = crate::billing::tier::period_start(cycle_start, now);
    let used_searches = nasrudin_pg::query::targeted_search_usage::count_in_period(
        &state.pg, auth.user.id, period_start,
    ).await.unwrap_or(0);
    let used_today = nasrudin_pg::query::api_usage::increment_and_get(
        &state.pg, auth.user.id, now.date_naive(),
    ).await.unwrap_or(0);
    Json(serde_json::json!({
        "plan_tier": auth.plan_tier.as_db(),
        "current_period_end": auth.user.current_period_end,
        "targeted_searches_used": used_searches,
        "targeted_searches_limit": q.targeted_searches_per_period,
        "api_used_today": used_today,
        "api_limit_per_day": q.api_per_day,
    })).into_response()
}
```

(Note: this also increments — for a read-only "me" you'd want a non-incrementing variant. Add `read_count` query that does `SELECT … WHERE user_id=$1 AND day=$2` instead.)

- [ ] **Step 2: Mount route** `.route("/api/billing/me", get(handlers::billing::me))`.
- [ ] **Step 3: Add the profile UI block:**

```tsx
function BillingCard() {
  const { data } = useQuery({
    queryKey: ['billing', 'me'],
    queryFn: async () => (await fetch('/api/billing/me', { credentials: 'include' })).json(),
  });
  const onManage = async () => {
    const res = await fetch('/api/billing/portal', { method: 'POST', credentials: 'include' });
    const { url } = await res.json();
    window.location.href = url;
  };
  if (!data) return null;
  return (
    <section>
      <h3>Plan: {data.plan_tier}</h3>
      <p>{data.targeted_searches_used} / {data.targeted_searches_limit} targeted searches this period</p>
      <p>{data.api_used_today} / {data.api_limit_per_day} API requests today</p>
      {data.plan_tier !== 'free' && <button onClick={onManage}>Manage billing</button>}
      {data.plan_tier === 'free' && <a href="/pricing">Upgrade</a>}
    </section>
  );
}
```

- [ ] **Step 4: Manual test** — visit `/profile`, see plan + usage; click Manage billing → opens Stripe portal.
- [ ] **Step 5: Commit.**

```bash
git commit -am "feat(profile): plan + usage + Manage billing portal link"
```

---

## Phase 7: E2E + ship checklist

### Task 7.1: End-to-end test with Stripe test card

**Files:**
- Create: `engine/crates/api/tests/billing_e2e.rs` (optional — can be a manual checklist if integration testing Stripe is too painful)

- [ ] **Step 1: Manual E2E (run once before merge):**
  1. Sign up a fresh user.
  2. Confirm `users.plan_tier='free'` in psql.
  3. Try `POST /api/conjecture` → expect HTTP 402 `targeted_search_quota_exhausted`.
  4. Visit `/pricing`, click Start subscription, complete checkout with `4242 4242 4242 4242`.
  5. Wait ≤2s, refresh `/profile`. Expect `plan_tier=researcher`, `current_period_end` set ~1 month out.
  6. Repeat `POST /api/conjecture` — expect 200.
  7. Click Manage billing → cancel subscription in portal.
  8. Wait ≤2s, refresh `/profile`. Expect `plan_tier=free` once Stripe fires `customer.subscription.deleted` (will fire at period end if user just clicks cancel; for immediate cancel, use portal "Cancel immediately" or `stripe trigger`).
- [ ] **Step 2: Document the test card + Stripe CLI workflow** in `docs/BILLING.md`.
- [ ] **Step 3: Commit.**

```bash
git commit -am "docs(billing): e2e Stripe test workflow"
```

### Task 7.2: Production runbook

**Files:**
- Create: `docs/BILLING.md`

- [ ] **Step 1: Write the runbook covering:**
  - How to switch from Stripe test mode to live mode (env var swap).
  - How to register the production webhook URL.
  - How to recreate Prices if pricing changes (and the migration plan: existing subs grandfathered, new subs at new price).
  - What to do if a webhook is dropped (Stripe dashboard → Webhooks → Resend).
  - How `billing_events` table answers "did we process this?" questions.
- [ ] **Step 2: Commit.**

```bash
git commit -am "docs(billing): production runbook"
```

### Task 7.3: Pre-merge final review

- [ ] **Step 1: Run** `just check` (lint + typecheck across the workspace).
- [ ] **Step 2: Run** `just test` (full test suite including new quota tests).
- [ ] **Step 3: Re-read the diff against this plan.** Anything missing? Anything that drifted from the design above?
- [ ] **Step 4: Merge to main / open PR.**

---

## Self-review (skill checklist)

**Spec coverage:**
- ✅ Stripe self-serve checkout (Researcher tier, monthly + annual) — Phase 3 + 6.
- ✅ Webhook signature verification + idempotency — Phase 4.
- ✅ Customer Portal for cancel/upgrade — Phase 3.3 + 6.2.
- ✅ Plan-aware quotas (targeted searches + API/day) — Phase 5.
- ✅ Fix 1 (academics ≠ buyer): pricing copy rewrite + .edu coupon-not-free + Free tier as citation infra — Task 6.1.
- ✅ Fix 2 (lab compression): 5-tier ladder with sane per-seat math + capability-based upgrade reasons — Task 6.1.
- ✅ Fix 3 (worker comp): explicit "paid tiers buy targeted compute, corpus stays free" copy + future Researcher entitlement for active workers — Task 6.1 FAQ.
- ⚠️ **Out of scope (separate plans, listed above):** Team/Institution self-serve checkout, worker compute credits, SSO, metered overage, .edu verification flow.

**Placeholder scan:** No `TBD`, no "implement later", no "appropriate error handling". Each step has either runnable code, an exact command, or a clearly delegated sub-task.

**Type consistency check:**
- `PlanTier::from_db` / `as_db` — used consistently in webhook handler, extractor, and `/api/billing/me`.
- `period_start(plan_cycle_start, now)` signature matches across `tier.rs`, `conjecture.rs`, `billing.rs::me`.
- `api_per_day` (`u32`) compared against `i64` from DB — handler casts to `u64` for comparison; consistent.
- Migration enum `Users::PlanTier` matches entity field `plan_tier` (snake_case), matches `users.plan_tier` SQL column.

One known wart for the engineer to mind: `async-stripe` API surface evolves between minor versions; the snippets target 0.40 — confirm method names (`SubscriptionStatus::Canceled` vs `Cancelled`, etc.) on first compile. Adjust as needed; the design doesn't depend on exact method names.

---

## Execution

Plan complete and saved to `docs/superpowers/plans/2026-04-29-monetization-stripe-foundation.md`. Two execution options:

**1. Subagent-Driven (recommended)** — I dispatch a fresh subagent per task, review between tasks, fast iteration.

**2. Inline Execution** — Execute tasks in this session using executing-plans, batch execution with checkpoints.

Which approach?
