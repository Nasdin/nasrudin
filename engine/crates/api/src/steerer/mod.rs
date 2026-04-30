//! LLM-driven cluster steerer.
//!
//! Every `STEERER_CADENCE_SECONDS` (default 600s) the daemon calls
//! Kimi K2.5 via DigitalOcean Gradient with a curated context: the last
//! N cycles' (config, outcome) pairs + an aggregate snapshot of user
//! demand + the set of paid Researcher jobs currently running. The
//! model returns a `SteeringConfig` that biases the GA exploration of
//! every connected worker. Workers fetch the new config at every chunk
//! boundary via `/api/seed` (which folds in the steering payload with
//! an ETag).
//!
//! Modes:
//!  * **C** (full authority) — emitted when no paid jobs are active.
//!    The model may set `mutation_knobs` and `hard_targets`.
//!  * **B** (mutation knobs locked) — emitted when ≥1 paid job is
//!    running. The model can only adjust `domain_weights`,
//!    `axiom_emphasis`, `fitness_weights`, and `soft_targets`. Hard
//!    targets and mutation-knob churn would destabilise the slot-hour
//!    accounting paid Researchers are billed against.
//!
//! On any failure (Gradient outage, parse error, validator reject)
//! the cycle reuses the most recent successfully-validated config.
//! See `cycle::run_one_cycle`.

pub mod bandit;
pub mod cycle;
pub mod demand;
pub mod outcome;
pub mod prompt;
pub mod schema;
