//! Physics Generator HTTP API library — shared between the daemon binary
//! and integration tests.

pub mod auth;
pub mod billing;
pub mod cache;
pub mod conjecture;
pub mod embed_cron;
pub mod handlers;
pub mod hydration;
pub mod jobs;
pub mod keygen;
pub mod lake_builder;
pub mod lake_promotion;
pub mod metrics;
pub mod pg_drain;
pub mod rate_limit;
pub mod reverify;
pub mod state;
pub mod steerer;
