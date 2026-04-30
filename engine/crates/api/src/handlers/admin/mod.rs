//! Admin-panel HTTP handlers. Every mutating handler in this module is
//! gated by `crate::admin::require_admin::RequireAdmin` and writes its
//! audit row through `crate::admin::audit::perform_audited`.

pub mod api_keys;
pub mod audit_log;
pub mod corpus;
pub mod jobs;
pub mod refund;
pub mod stats;
pub mod steering;
pub mod users;
