//! Admin-panel infrastructure.
//!
//! Modules:
//! - `audit` — frozen action taxonomy + `perform_audited` invariant helper.
//! - `require_admin` — RequireAdmin extractor (session OR ADMIN_TOKEN bearer).

pub mod audit;
pub mod require_admin;
