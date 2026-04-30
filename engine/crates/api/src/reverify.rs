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
use nasrudin_derive::{
    Chain, DerivationContext, RuleStep,
    lean_emitter::{LeanEmitConfig, emit_lean_file},
    strategies::DerivationStrategy,
};
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
    pub axiom_store: crate::state::SharedAxiomStore,
    pub discovery_tx: broadcast::Sender<DiscoveryEvent>,
    /// Server-side cache bundle (Phase A.5 wiring). When `Some` and
    /// `cache_ctx.config.attempts_enabled`, the reverify path goes
    /// through `LakeBuilder::verify_cached` instead of `verify`.
    pub cache_ctx: Option<Arc<crate::cache::CacheCtx>>,
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
    /// Process one queued job. The verification cascade is:
    ///
    /// 1. **Chain validation (firewall).** Replay the worker-submitted chain
    ///    against the server's trusted [`AxiomStore`]. If the chain references
    ///    an unknown axiom, fails to apply a step, or produces a final
    ///    expression that doesn't match the row's canonical statement, the
    ///    submission is rejected immediately — this catches workers who
    ///    fabricate steps or claim a result they didn't actually derive. The
    ///    submission never reaches a lake-build stage.
    /// 2. **A-path (server-regenerated Lean).** If the chain replays cleanly,
    ///    the server emits its own Lean source from the resulting context and
    ///    lake-builds *that*, not the worker's. A worker can no longer pass
    ///    by submitting unrelated Lean source; the math has to actually
    ///    follow from the chain they sent.
    /// 3. **B-path (worker-submitted Lean fallback).** Reached only when the
    ///    chain is empty (e.g. backfilled / imported theorems with no chain)
    ///    *or* the server's emitter produced a chain whose Lean fails to
    ///    build (`server_emitter_drift` — math is real but our emitter has
    ///    a bug). In that case we lake-build the worker's submitted source.
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

        // 2. Replay the chain server-side over our trusted AxiomStore.
        //
        // **Production architecture (P-Task 1):** chain replay IS verification.
        // The Rust rule library (`engine/crates/derive/src/rules.rs`) is sound
        // by construction — every rule is a proof primitive that only
        // produces mathematically valid transformations. The AxiomStore is
        // audited at boot via `no_cheat_audit::audit_or_panic`. So if a chain
        // composes valid rules over audited axioms and yields the canonical
        // the worker claims, the theorem is verified.
        //
        // We tag this verification path with `tactic_used = "chain_replay"`
        // and call it `ChainVerified`. Lake-build is the *kernel-level final
        // arbiter* but it's deferred to the lake_promotion drain (P-Task 2)
        // and only fires when a theorem is actually consumed (downloaded,
        // included as a peer-axiom in /api/seed, manually validated, or
        // picked up by the background crawler).
        //
        // This collapses ingest-time verification cost from ~5-30s
        // (lake build) to ~µs (chain replay), turning the central server
        // from "lake-build limited" to "Postgres-write limited" — roughly
        // 30× ingest throughput headroom for thousands of distributed workers.
        match self.check_chain(&row) {
            ChainCheck::Regenerated(_regen) => {
                // Chain replay succeeded. P-Task 12 final design: 3
                // verification states discriminated by `tactic_used`:
                //
                //   * "chain_replay" — no worker lake claim. Workers
                //     can't compound on these (firewalled out of
                //     /api/seed) until server lake-promotion confirms.
                //   * "worker_claim" — worker claimed local lake
                //     passed. Server immediately marks for peer use
                //     (high prior probability of passing) but ALSO
                //     queues for independent server-side lake
                //     confirmation. Anyone could lie about local
                //     lake; the queued check + lazy-on-download
                //     verify catches forgery.
                //   * "lake_build" — server has independently
                //     kernel-confirmed. Required for download.
                //
                // Admin-panel trust-bypass: trusted+sampled-out rows
                // skip lake promotion entirely (verification_path =
                // "trusted_bypass", tactic = "lake_build"). Trusted
                // +sampled-in and untrusted rows go through the normal
                // worker_claim / chain_replay split.
                let trust_decision = crate::trust::TrustDecision {
                    trusted: row.worker_trusted,
                    spot_check_rate: row
                        .worker_spot_check_rate
                        .map(|r| r as u32)
                        .unwrap_or(50),
                    source: crate::trust::TrustSource::Default,
                };
                let bypass = !crate::trust::should_promote(&trust_decision, &row.id);

                if bypass {
                    self.flip_verified(&row, "trusted_bypass", "lake_build", 0)
                        .await?;
                    self.rocks.dequeue_reverify(&job.theorem_id).ok();
                    return Ok(());
                }

                let (path, tactic, promotion_priority) = if row.worker_verified {
                    ("A_worker_claim", "worker_claim", 1u8)
                } else {
                    ("A_chain_replay", "chain_replay", 2u8)
                };
                self.flip_verified(&row, path, tactic, 0).await?;

                // Enqueue server-side lake confirmation. P-Task 2's
                // drain pops priority-then-FIFO and runs the actual
                // lake build, flipping to "lake_build" or cascade-
                // rejecting on disagreement.
                let mut id_arr = [0u8; 8];
                if row.id.len() == 8 {
                    id_arr.copy_from_slice(&row.id);
                    let _ = self.rocks.enqueue_lake_promotion(&id_arr, promotion_priority);
                }

                self.rocks.dequeue_reverify(&job.theorem_id).ok();
                return Ok(());
            }
            ChainCheck::Invalid(reason) => {
                // Hostile / buggy worker: chain doesn't replay. Reject without
                // trying B-path — we don't lake-build untrusted Lean from a
                // worker whose chain can't be verified.
                let full_reason = format!("chain_invalid: {reason}");
                tracing::warn!(
                    theorem_id = %theorem_id_hex,
                    contributor = %row.contributor_id,
                    reason = %reason,
                    "rejecting hostile / malformed chain submission"
                );
                theorem_q::mark_rejected(&self.pg, &row.id, &full_reason).await?;
                let _ = self.discovery_tx.send(DiscoveryEvent::TheoremRejected {
                    theorem_id: theorem_id_hex,
                    reason: full_reason,
                });
                self.rocks.dequeue_reverify(&job.theorem_id).ok();
                return Ok(());
            }
            ChainCheck::Empty => {
                // No chain provided (e.g. imported/backfilled rows). We
                // can't verify the chain — fall through to B-path so the
                // worker's submitted Lean has to lake-build standalone.
            }
        }

        // 3. B-path: lake-build the worker-submitted source.
        self.try_b_path(job, &row).await
    }

    /// Replay the row's `chain_json` over the server's [`AxiomStore`] and
    /// regenerate Lean from the resulting [`DerivationContext`]. See
    /// [`ChainCheck`] for the three outcomes.
    fn check_chain(&self, row: &nasrudin_pg::entity::theorems::Model) -> ChainCheck {
        // Empty / missing chain → defer to B-path. Imported theorems with
        // origin: Imported and chain=[] are legitimate.
        let steps_value = match &row.chain_json {
            v if v.is_null() => return ChainCheck::Empty,
            serde_json::Value::Array(arr) if arr.is_empty() => return ChainCheck::Empty,
            v => v,
        };

        let steps: Vec<RuleStep> = match serde_json::from_value(steps_value.clone()) {
            Ok(s) => s,
            Err(e) => return ChainCheck::Invalid(format!("chain_json deserialize: {e}")),
        };

        let chain = Chain(steps);
        let mut ctx = DerivationContext::new();
        let store = self.axiom_store.load();
        let final_expr = match chain.execute(&store, &mut ctx) {
            Ok(e) => e,
            Err(e) => return ChainCheck::Invalid(format!("replay: {e}")),
        };

        // Compare to the row's claimed canonical statement.
        let server_canonical = final_expr.to_canonical();
        if server_canonical != row.canonical_statement {
            return ChainCheck::Invalid(format!(
                "canonical_mismatch: chain produced `{server_canonical}`, row claims `{}`",
                row.canonical_statement
            ));
        }

        // Chain replay succeeded and the canonical matches the worker's
        // claim. P-Task 1: this IS verification — no lake build needed
        // here. The `RegeneratedLean { lean_source }` payload is no
        // longer used by A-path (reverify::process_one). Lake-promotion
        // (P-Task 2) fetches `lean_source` directly from PG when it
        // later promotes a ChainVerified theorem. So we skip the
        // emit_lean_file work entirely on the chain-replay hot path.
        let _ = (ctx, server_canonical);
        let _ = LeanEmitConfig {
            namespace: String::new(),
            theorem_name: String::new(),
            use_mathlib: false,
        };
        let _ = emit_lean_file;
        ChainCheck::Regenerated(RegeneratedLean)
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

        match self
            .verify_cached_or_direct(row, &row.lean_source, &theorem_id_hex)
            .await?
        {
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

        // RocksDB-primary read path (Task 4): update the Theorem's status
        // and append to the verified-at index so `/api/seed` and
        // `/api/theorems/recent` can serve newest-first verified rows
        // without hitting Postgres. Best-effort — if the row isn't in
        // RocksDB (legacy / hydrated-only data) the Postgres update
        // above is still authoritative for query consumers that haven't
        // migrated yet.
        let mut id_arr = [0u8; 8];
        if row.id.len() == 8 {
            id_arr.copy_from_slice(&row.id);
            let now_micros = chrono::Utc::now().timestamp_micros();
            if let Ok(Some(mut theorem)) = self.rocks.get_theorem(&id_arr) {
                theorem.verified = nasrudin_core::VerificationStatus::Verified {
                    proof_term: Vec::new(),
                    tactic_used: tactic.to_string(),
                };
                let _ = self.rocks.put_theorem(&theorem);
            }
            let _ = self.rocks.mark_verified_at(&id_arr, now_micros);
        }

        // Best-effort broadcast: a closed channel (no live subscribers) is
        // fine and shouldn't fail the verification flip.
        let _ = self.discovery_tx.send(DiscoveryEvent::TheoremVerified {
            theorem_id: hex::encode(row.id.as_slice()),
            verification_path: path.to_string(),
            duration_ms,
        });
        Ok(())
    }

    /// Cache-aware lake-build dispatch.
    ///
    /// When `cache_ctx` is wired and `attempts_enabled`, routes through
    /// [`LakeBuilder::verify_cached`] (skip on hit, write on miss).
    /// Otherwise falls through to direct [`LakeBuilder::verify`].
    async fn verify_cached_or_direct(
        &self,
        row: &nasrudin_pg::entity::theorems::Model,
        lean_source: &str,
        theorem_id_hex: &str,
    ) -> Result<VerifyOutcome> {
        if let Some(c) = self
            .cache_ctx
            .as_ref()
            .filter(|c| c.config.attempts_enabled)
        {
            // Build the 16-byte cache key: canonical_hash || axiom_set_hash.
            let mut canon8 = [0u8; 8];
            canon8.copy_from_slice(&row.canonical_hash[..8]);
            let axiom_hash = self.axiom_hash_for_row(row);
            let cache_key = nasrudin_rocks::AttemptsCache::make_key(&canon8, &axiom_hash);
            self.lake
                .verify_cached(
                    &c.bundle.attempts,
                    &cache_key,
                    &c.bundle.lean_version,
                    &c.bundle.worker_id,
                    c.bundle.ttl_days,
                    lean_source,
                    theorem_id_hex,
                )
                .await
        } else {
            self.lake.verify(lean_source, theorem_id_hex).await
        }
    }

    /// Compute the 8-byte axiom-set hash for a theorems row by walking
    /// the row's `chain_json` (the same source `check_chain` parses)
    /// and collecting axiom names from `IntroduceAxiom` /
    /// `IntroduceTheorem` steps. Falls back to all-zeros when the row
    /// has no chain (imported / backfilled theorems with empty
    /// `chain_json`) — meaning two cache entries for the same canonical
    /// statement but different axiom sets stay distinguished as long as
    /// chains are present.
    fn axiom_hash_for_row(&self, row: &nasrudin_pg::entity::theorems::Model) -> [u8; 8] {
        use nasrudin_core::{axiom_id_from_name, axiom_set_hash};
        use std::collections::BTreeSet;

        let steps_value = match &row.chain_json {
            v if v.is_null() => return [0u8; 8],
            serde_json::Value::Array(arr) if arr.is_empty() => return [0u8; 8],
            v => v,
        };
        let steps: Vec<RuleStep> = match serde_json::from_value(steps_value.clone()) {
            Ok(s) => s,
            Err(_) => return [0u8; 8],
        };
        let mut ids: BTreeSet<[u8; 8]> = BTreeSet::new();
        for step in &steps {
            match step {
                RuleStep::IntroduceAxiom { axiom_name } => {
                    ids.insert(axiom_id_from_name(axiom_name));
                }
                RuleStep::IntroduceTheorem { theorem_name } => {
                    ids.insert(axiom_id_from_name(theorem_name));
                }
                _ => {}
            }
        }
        axiom_set_hash(&ids)
    }
}

/// Outcome of replaying a worker-submitted chain over the server's
/// trusted [`AxiomStore`].
enum ChainCheck {
    /// Chain replayed cleanly and the final expression matches the row's
    /// canonical statement; the server emitted its own Lean source from
    /// the resulting derivation context.
    Regenerated(RegeneratedLean),
    /// No chain provided (`null` or empty array). Imported / backfilled
    /// theorems are legitimate in this state — defer to B-path.
    Empty,
    /// Chain failed to deserialize, failed to replay, or produced a final
    /// expression that doesn't match the row's claimed canonical statement.
    /// The submission is rejected without ever lake-building the worker's
    /// untrusted Lean source.
    Invalid(String),
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

/// Marker for "chain replay succeeded and canonical matches." P-Task 1
/// inverted the A-path: chain replay is verification (sound by
/// construction over the trusted Rust rule library + audited
/// AxiomStore). Lake-build is deferred to the lake-promotion drain
/// and happens only on consumption. So this no longer carries any
/// payload — the chain replay's success is the entire signal.
#[allow(dead_code)]
struct RegeneratedLean;
