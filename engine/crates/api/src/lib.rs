//! Physics Generator HTTP API library — shared between the daemon binary
//! and integration tests.

pub mod admin;
pub mod auth;
pub mod firebase_auth;
pub mod impersonation;
pub mod billing;
pub mod cache;
pub mod conjecture;
pub mod embed_cron;
pub mod handlers;
pub mod hydration;
/// Re-export of the headline registry from `nasrudin-derive` so all
/// API call sites that used `crate::headline_registry::match_canonical`
/// keep working. The single source of truth now lives in the derive
/// crate so the Lean emitter can use the same names + descriptions.
pub use nasrudin_derive::headline_registry;
pub mod jobs;
pub mod keygen;
pub mod lake_builder;
pub mod lake_promotion;
pub mod metrics;
pub mod pg_drain;
pub mod platform_targets;
pub mod rate_limit;
pub mod reverify;
pub mod state;
pub mod steerer;
pub mod theorem_naming;
pub mod trust;
