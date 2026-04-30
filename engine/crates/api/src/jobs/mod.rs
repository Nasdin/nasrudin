//! Paid Researcher job lifecycle support — claim, heartbeat, capacity.
//!
//! See `docs/superpowers/specs/2026-04-30-cluster-steerer-and-paid-research-design.md`.
//! The user-facing handlers live in `handlers::research_jobs`; the
//! atomic claim + lease + heartbeat protocol lives in
//! `handlers::jobs_claim` and reads/writes through this module.

pub mod capacity;
pub mod quota;
pub mod reaper;

use serde::{Deserialize, Serialize};

/// Events fanned out to paid-job SSE subscribers (the user watching
/// their conjecture run live). Emitted by handlers + the heartbeat
/// path.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum JobEvent {
    JobState {
        state: String,
    },
    Progress {
        candidates_attempted: i32,
        candidates_verified: i32,
        best_fitness: f32,
        best_chain_length: i32,
        lake_slot_hours_consumed: f32,
    },
    TheoremVerified {
        theorem_id_hex: String,
        statement_latex: String,
    },
    Proved {
        lean_url: String,
    },
    BudgetExhausted {
        best_partial_summary: String,
        refund_credits: i32,
    },
    Cancelled,
}
