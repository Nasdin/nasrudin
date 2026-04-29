//! Billing — Stripe-backed subscriptions, plan-aware quotas, and the
//! webhook handler that keeps `users.plan_tier` in sync with Stripe.

pub mod stripe_client;
pub mod tier;
pub mod webhook;

pub use tier::{period_start, PlanTier, Quotas};
