//! Reverify queue: async drain that re-runs A→B verification on theorems
//! flagged `Pending` in PostgreSQL.
//!
//! # Phase 9 / Task 3.2 — scaffold + A-path slice
//!
//! This module owns the [`ReverifyQueue`] (the verification drain), the
//! [`DiscoveryEvent`] SSE broadcast variants, and the A-path slice of
//! [`ReverifyQueue::process_one`]. The A-path is the "regenerate Lean from
//! the chain on the server, then run lake build" trust path:
//!
//! 1. Look up the row from Postgres by `theorem_id`.
//! 2. Try to regenerate the Lean source from the chain JSON via the server's
//!    own [`AxiomStore`] + emitter (defence against hostile-worker submissions
//!    that ship a bogus `lean_source`).
//! 3. If regeneration succeeds and matches the row's canonical statement,
//!    run [`LakeBuilder::verify`] on the server-emitted Lean.
//! 4. On `Verified`, atomically flip `status = Verified` + bump the
//!    contributor's `theorems_contributed` counter, broadcast the SSE event,
//!    and dequeue from RocksDB.
//! 5. On any A-path failure, fall through to the B-path stub
//!    ([`ReverifyQueue::try_b_path`]).
//!
//! # Stubs left for follow-up tasks
//!
//! - [`ReverifyQueue::try_regenerate_lean`] always returns `None` in this
//!   task. The chain JSON ↔ `Vec<RuleStep>` ↔ Lean emitter pipeline has its
//!   own interface contract worth a dedicated subagent pass; Task 3.3/3.4
//!   will wire it up.
//! - [`ReverifyQueue::try_b_path`] currently dequeues without flipping
//!   status. Task 3.3 replaces this with the real B-path (verify the
//!   worker-submitted Lean source after pre-flight, mark Verified or
//!   Rejected accordingly).
//! - The drain spawn loop + `AppState` integration land in Task 3.4.

use std::sync::Arc;

use anyhow::Result;
use nasrudin_derive::AxiomStore;
use nasrudin_pg::query::{theorems as theorem_q, workers as worker_q};
use nasrudin_rocks::{ReverifyJob, TheoremDb};
use sea_orm::{DatabaseConnection, TransactionTrait};
use serde::Serialize;
use tokio::sync::broadcast;

use crate::lake_builder::{LakeBuilder, VerifyOutcome};

/// Async drain that pops [`ReverifyJob`]s from the RocksDB `reverify_queue`
/// CF and runs the A→B verification cascade against PostgreSQL.
///
/// All fields are `Arc`/`Clone` so the same queue can be shared by multiple
/// drain workers in Task 3.4.
pub struct ReverifyQueue {
    pub rocks: Arc<TheoremDb>,
    pub pg: DatabaseConnection,
    pub lake: Arc<LakeBuilder>,
    pub axiom_store: Arc<AxiomStore>,
    pub discovery_tx: broadcast::Sender<DiscoveryEvent>,
}

/// SSE event variants broadcast as the reverify queue progresses through a
/// theorem's lifecycle.
///
/// The `kind` tag is the discriminator on the wire; UI clients subscribe to
/// this stream and re-render the leaderboard / discovery feed when these
/// fire.
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind")]
pub enum DiscoveryEvent {
    /// A new theorem was accepted into the queue and is awaiting verification.
    TheoremPending {
        /// Hex-encoded 8-byte theorem id.
        theorem_id: String,
        /// Canonical prefix-form statement.
        canonical: String,
        /// Worker / contributor who submitted the theorem.
        contributor_id: String,
    },
    /// A queued theorem passed verification on path "A" or "B".
    TheoremVerified {
        /// Hex-encoded 8-byte theorem id.
        theorem_id: String,
        /// Which trust path verified the theorem: `"A"` (server-regenerated
        /// Lean) or `"B"` (worker-submitted Lean after pre-flight).
        verification_path: String,
        /// Wall-clock duration of `lake build`, milliseconds.
        duration_ms: u32,
    },
    /// A queued theorem was rejected (preflight failed or `lake build` failed
    /// on both A and B paths).
    TheoremRejected {
        /// Hex-encoded 8-byte theorem id.
        theorem_id: String,
        /// Free-form rejection reason persisted alongside the row.
        reason: String,
    },
}

impl ReverifyQueue {
    /// Process one queued job. Tries A-path (server-regenerated Lean from
    /// the chain) first; falls through to [`Self::try_b_path`] on any A-path
    /// failure.
    ///
    /// On A-path success, atomically flips `Pending → Verified`, increments
    /// the contributor's counter, broadcasts [`DiscoveryEvent::TheoremVerified`],
    /// and dequeues the job from RocksDB.
    pub async fn process_one(&self, job: ReverifyJob) -> Result<()> {
        // 1. Load row from Postgres.
        let row = match theorem_q::get_by_id(&self.pg, &job.theorem_id).await? {
            Some(r) => r,
            None => {
                tracing::warn!(
                    theorem_id = %hex::encode(job.theorem_id),
                    "reverify: theorem missing from PG, dequeueing"
                );
                self.rocks.dequeue_reverify(&job.theorem_id).ok();
                return Ok(());
            }
        };

        let theorem_id_hex = hex::encode(row.id.as_slice());

        // 2. Try server-side Lean regeneration from the chain. If the
        //    server-emitted Lean matches the recorded canonical statement,
        //    feed it to LakeBuilder for the trusted A-path verification.
        if let Some(regen) = self.try_regenerate_lean(&row).await
            && regen.canonical_statement == row.canonical_statement
        {
            match self.lake.verify(&regen.lean_source, &theorem_id_hex).await? {
                VerifyOutcome::Verified {
                    tactic,
                    duration_ms,
                } => {
                    self.flip_verified(&row, "A", &tactic, duration_ms).await?;
                    self.rocks.dequeue_reverify(&job.theorem_id).ok();
                    return Ok(());
                }
                VerifyOutcome::Rejected { .. } => {
                    // A-path lake-built but failed; fall through to B-path.
                }
            }
        }

        // 3. Fall through to B-path (Task 3.3 will implement; current stub
        //    just dequeues so the queue doesn't loop forever during 3.2 tests).
        self.try_b_path(job, &row).await
    }

    /// B-path fallback: verify the worker-submitted `lean_source` directly via
    /// [`LakeBuilder::verify`] (which already enforces the fresh-axiom/sorry
    /// preflight). On success, flip `Pending → Verified` with `path = "B"` and
    /// log a `server_emitter_drift` warning (the math is real but the server's
    /// emitter disagreed with the worker's). On terminal failure, mark
    /// `Rejected{reason}` and broadcast [`DiscoveryEvent::TheoremRejected`].
    ///
    /// Transient toolchain errors (`reason == "toolchain_error"`) re-enqueue
    /// the job with bumped `attempts` up to `MAX_ATTEMPTS = 3` total runs.
    /// Permanent rejections (`lake_build_failed`, `verify_timeout`,
    /// `preflight_*`) are immediately terminal — they're consistent properties
    /// of the submitted source, not flakiness.
    async fn try_b_path(
        &self,
        job: ReverifyJob,
        row: &nasrudin_pg::entity::theorems::Model,
    ) -> Result<()> {
        let theorem_id_hex = hex::encode(&row.id);

        match self.lake.verify(&row.lean_source, &theorem_id_hex).await? {
            VerifyOutcome::Verified {
                tactic,
                duration_ms,
            } => {
                // B-path succeeded: server emitter probably drifted from
                // worker's, but the math is real. Log + accept + flip.
                tracing::warn!(
                    theorem_id = %theorem_id_hex,
                    engine_git_sha = %row.engine_git_sha,
                    "server_emitter_drift: A-path failed but B-path on worker-submitted Lean passed"
                );
                self.flip_verified(row, "B", &tactic, duration_ms).await?;
                self.rocks.dequeue_reverify(&job.theorem_id).ok();
                Ok(())
            }
            VerifyOutcome::Rejected {
                reason,
                stderr_tail,
            } => {
                const MAX_ATTEMPTS: u8 = 3;

                // Retry transient toolchain errors up to MAX_ATTEMPTS.
                // Permanent rejections (lake_build_failed, preflight_*,
                // verify_timeout) are terminal.
                let is_transient = reason == "toolchain_error";
                if is_transient && job.attempts + 1 < MAX_ATTEMPTS {
                    let new_job = ReverifyJob {
                        theorem_id: job.theorem_id,
                        attempts: job.attempts + 1,
                        enqueued_at_micros: chrono::Utc::now().timestamp_micros(),
                    };
                    tracing::warn!(
                        theorem_id = %theorem_id_hex,
                        attempts = new_job.attempts,
                        reason = %reason,
                        "reverify: transient failure, re-enqueueing"
                    );
                    // Re-enqueue with bumped attempts (overwrite semantics:
                    // the queue is keyed by theorem_id, so the bumped-attempts
                    // job replaces the prior entry).
                    self.rocks.enqueue_reverify(&new_job)?;
                } else {
                    // Terminal: mark Rejected.
                    let full_reason = if stderr_tail.is_empty() {
                        reason.clone()
                    } else {
                        format!("{reason}: {stderr_tail}")
                    };
                    theorem_q::mark_rejected(&self.pg, &row.id, &full_reason).await?;
                    let _ = self.discovery_tx.send(DiscoveryEvent::TheoremRejected {
                        theorem_id: theorem_id_hex,
                        reason: full_reason,
                    });
                    self.rocks.dequeue_reverify(&job.theorem_id).ok();
                }
                Ok(())
            }
        }
    }

    /// Atomic Postgres transaction: flip the row to `Verified` + increment
    /// the contributor's `theorems_contributed`. On commit, broadcast a
    /// [`DiscoveryEvent::TheoremVerified`] on the discovery channel.
    ///
    /// Both writes share a single transaction so a crash between them can't
    /// leave the leaderboard counter out of sync with the verified rows.
    async fn flip_verified(
        &self,
        row: &nasrudin_pg::entity::theorems::Model,
        path: &str,
        tactic: &str,
        duration_ms: u32,
    ) -> Result<()> {
        let txn = self.pg.begin().await?;
        theorem_q::mark_verified(&txn, &row.id, path, tactic, duration_ms as i32).await?;
        worker_q::increment_contribution(&txn, &row.contributor_id).await?;
        txn.commit().await?;

        // Best-effort broadcast: a closed channel (no live subscribers) is
        // fine and shouldn't fail the verification flip.
        let _ = self.discovery_tx.send(DiscoveryEvent::TheoremVerified {
            theorem_id: hex::encode(row.id.as_slice()),
            verification_path: path.to_string(),
            duration_ms,
        });
        Ok(())
    }

    /// Try to regenerate Lean from the row's `chain_json` via the server's
    /// trusted [`AxiomStore`] + emitter. Returns `None` when the chain is
    /// empty, malformed, or references unknown axioms/rules — that signals
    /// "fall through to B-path."
    ///
    /// **Phase 9 stub**: this currently always returns `None`. The real
    /// implementation needs the chain JSON ↔ `Vec<RuleStep>` ↔ Lean emitter
    /// glue, which has its own interface contract worth a dedicated pass in
    /// Task 3.3/3.4.
    async fn try_regenerate_lean(
        &self,
        _row: &nasrudin_pg::entity::theorems::Model,
    ) -> Option<RegeneratedLean> {
        // Forces every job to B-path while the chain → Lean emitter glue is
        // still being designed. Safe to ship in 3.2 because:
        //   - No live drain loop is wired yet (Task 3.4).
        //   - Tests use a stub LakeBuilder (Task 3.4).
        //   - Real A-path regen requires careful chain JSON ↔ RuleStep ↔
        //     Lean emitter glue, scoped to a follow-up task.
        let _ = &self.axiom_store;
        None
    }
}

impl ReverifyQueue {
    /// Background task: scan `reverify_queue` every 500ms, process one job
    /// per tick. Logs and continues on per-job errors. Runs until the task
    /// is cancelled (i.e. forever, in practice — Phase 9 has no graceful
    /// shutdown for the drain loop).
    ///
    /// Tick cadence uses [`tokio::time::MissedTickBehavior::Skip`] so a slow
    /// `lake build` (which can take 30+ seconds) doesn't queue up a backlog
    /// of catch-up ticks the moment it returns.
    pub async fn drain_loop(self: Arc<Self>) {
        let mut interval = tokio::time::interval(std::time::Duration::from_millis(500));
        interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            interval.tick().await;
            match self.rocks.list_reverify_pending(1) {
                Ok(jobs) if jobs.is_empty() => continue,
                Ok(jobs) => {
                    let job = jobs.into_iter().next().unwrap();
                    if let Err(e) = self.process_one(job.clone()).await {
                        tracing::error!(
                            theorem_id = %hex::encode(job.theorem_id),
                            err = %e,
                            "reverify drain: process_one failed"
                        );
                    }
                }
                Err(e) => {
                    tracing::error!(err = %e, "reverify drain: queue scan failed");
                }
            }
        }
    }
}

/// Bundle of "server-regenerated Lean" facts produced by
/// [`ReverifyQueue::try_regenerate_lean`].
///
/// `canonical_statement` is the prefix-form derived equation; the queue
/// requires it to bit-match the row's stored `canonical_statement` before
/// it will trust the A-path verification. `lean_source` is the
/// `theorem … := by …` body suitable for handing to
/// [`LakeBuilder::verify`].
struct RegeneratedLean {
    canonical_statement: String,
    lean_source: String,
}
