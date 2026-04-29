//! Physics Generator HTTP API library — shared between the daemon binary
//! and integration tests.

pub mod auth;
pub mod cache;
pub mod conjecture;
pub mod embed_cron;
pub mod handlers;
pub mod hydration;
pub mod keygen;
pub mod lake_builder;
pub mod lake_promotion;
pub mod pg_drain;
pub mod rate_limit;
pub mod reverify;
pub mod state;
