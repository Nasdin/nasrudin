//! Admin-panel infrastructure.
//!
//! Modules:
//! - `audit` — frozen action taxonomy + `perform_audited` invariant helper.
//! - `require_admin` — RequireAdmin extractor (session OR ADMIN_TOKEN bearer).

pub mod audit;
pub mod bulk_runner;
pub mod impersonation_expiry;
pub mod require_admin;
