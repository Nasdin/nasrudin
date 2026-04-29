//! Conjecture loop: server-side LLM call + state machine for
//! `conjecture_jobs`. Worker-side claim/heartbeat/submit lands in
//! Phase E and will plug into the same broadcast channel.

pub mod orchestrate;
pub mod prompt;
pub mod types;

pub use types::*;

use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// In-process event published whenever a conjecture row mutates.
/// SSE handlers subscribe to a `broadcast::Sender<ConjectureEvent>` on
/// `AppState` and filter by `job_id`. Persisted twin lives in the
/// `conjecture_events` table for replay.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConjectureEvent {
    pub id: i64,
    pub job_id: Uuid,
    pub kind: String,
    pub payload: serde_json::Value,
    pub at: chrono::DateTime<chrono::Utc>,
}
