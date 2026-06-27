//! Billing — Stripe-backed subscriptions, plan-aware quotas, and the
//! webhook handler that keeps `users.plan_tier` in sync with Stripe.

pub mod api_quota_layer;
pub mod refund;
pub mod refund_reconciler;
pub mod sponsorship_backfill;
pub mod stripe_client;
pub mod tier;
pub mod webhook;

pub use tier::{PlanTier, Quotas, period_start};
