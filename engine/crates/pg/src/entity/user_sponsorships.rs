//! `user_sponsorships` — durable record of every donation /
//! subscription event for the public-profile sponsorship badge.
//!
//! See migration `m20260430_000030_user_sponsorships`. Both
//! one-time donations and recurring subscriptions live in the same
//! table; the `kind` column distinguishes them and CHECK constraints
//! enforce that the matching `stripe_*_id` is set.

use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq, DeriveEntityModel)]
#[sea_orm(table_name = "user_sponsorships")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    pub user_id: Uuid,
    /// Stripe event id that produced this row. NULL on backfill rows
    /// (synthesised from API queries with no originating event).
    /// Unique-when-set via partial index.
    pub stripe_event_id: Option<String>,
    /// `'subscription'` or `'one_time'`. CHECK-constrained.
    pub kind: String,
    /// `'sponsor_5'`, `'sponsor_25'`, `'sponsor_100'`, `'sponsor_open'`,
    /// `'researcher_monthly'`, `'researcher_annual'`, or NULL when the
    /// price doesn't map to a known tier (e.g. legacy or test prices).
    pub tier: Option<String>,
    /// Cents at the time of the event. Always set for one-time;
    /// subscription rows store the per-interval price.
    pub amount_cents: Option<i64>,
    pub currency: String,
    /// Set on subscription rows; UNIQUE.
    pub stripe_subscription_id: Option<String>,
    /// Set on one-time rows; UNIQUE.
    pub stripe_charge_id: Option<String>,
    /// `'active'`, `'canceled'`, `'completed'`, or `'refunded'`.
    pub status: String,
    pub started_at: DateTimeWithTimeZone,
    pub canceled_at: Option<DateTimeWithTimeZone>,
    pub created_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
