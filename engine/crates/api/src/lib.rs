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
pub mod headline_registry;
pub mod hydration;
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
pub mod trust;
