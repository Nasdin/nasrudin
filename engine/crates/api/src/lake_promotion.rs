//! Lazy lake-build promotion drain (P-Task 2).
//!
//! After P-Task 1 inverted the verification path so chain-replay alone
//! produces `Verified { tactic_used: "chain_replay" }` (ChainVerified)
//! rows, we still need a kernel-level final arbiter for theorems that
//! actually get *consumed* — downloaded as `.lean` source, included
//! as peer-axioms in `/api/seed`, manually validated by a user, or
//! picked up by the background crawler. That's this module.
//!
//! ## Architecture
//!
//! Three priority lanes in the `CF_LAKE_PROMOTION_QUEUE` column family:
//!
//! - **Priority 0** — manual user trigger via `POST /api/theorems/{id}/verify`
//!   (P-Task 4) and synchronous download via `lean_download`. Drained first.
//! - **Priority 1** — seed-inclusion demand. When `/api/seed` filters a
//!   ChainVerified theorem out of the response, it enqueues at p1 so the
//!   theorem gets graduated quickly enough to participate in the next
//!   /api/seed payload.
//! - **Priority 2** — background crawler. Walks `CF_THEOREMS` periodically
//!   and enqueues every ChainVerified row, ensuring eventual consistency
//!   regardless of consumption.
//!
//! ## Wakeup
//!
//! Synchronous callers (manual verify + download) park on a
//! `tokio::sync::Notify` keyed by `theorem_id`. The drain task fires the
//! notification on completion so the caller wakes within ms of lake build
//! returning.
//!
//! ## Cascade
//!
//! On lake-rejection the drain calls `rocks.cascade_reject(id, reason)`
//! (P-Task 3) which BFS-walks the lineage graph and invalidates every
//! descendant. This is what prevents a single bad theorem from polluting
//! the corpus.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

use anyhow::Result;
use chrono::Utc;
use sea_orm::DatabaseConnection;
use tokio::sync::{Mutex, Notify};

use nasrudin_core::TheoremId;
use nasrudin_pg::query::theorems as theorem_q;
use nasrudin_pg::query::workers as worker_q;
use nasrudin_rocks::TheoremDb;

use crate::lake_builder::{LakeBuilder, VerifyOutcome};
use crate::reverify::DiscoveryEvent;

/// How often the drain checks the queue. 250ms strikes a balance: low
/// enough that synchronous callers don't park long, high enough that
/// the loop doesn't burn CPU when the queue is empty.
const DRAIN_INTERVAL: Duration = Duration::from_millis(250);
/// How many entries to drain per tick. The lake-build pool is
/// concurrency-limited by its own semaphore (`LakeBuilder::semaphore`),
/// so dequeuing more than that just queues internally — fine.
const BATCH_SIZE: usize = 16;
/// Background crawler enqueue cadence. Every 5 minutes we walk
/// `CF_THEOREMS` and enqueue any ChainVerified row not already in the
/// queue at priority 2. Bounded scan so it doesn't pin a thread on a
/// million-row store.
const CRAWLER_INTERVAL: Duration = Duration::from_secs(300);
const CRAWLER_BATCH: usize = 10_000;

/// Shared promotion state — held by the drain task and exposed to
/// handlers that need to wait for a specific theorem's outcome
/// (`/api/theorems/{hash}/lean` synchronous download, `/api/theorems/{id}/verify`
/// manual trigger).
pub struct LakePromotion {
    pub rocks: Arc<TheoremDb>,
    pub pg: DatabaseConnection,
    pub lake: Arc<LakeBuilder>,
    pub discovery_tx: tokio::sync::broadcast::Sender<DiscoveryEvent>,
    /// Per-theorem-id wakeup notifiers. Created lazily on first
    /// `await_promotion` call. The drain calls `notify_waiters()` after
    /// each definitive outcome so awaiters return.
    notifiers: Mutex<HashMap<TheoremId, Arc<Notify>>>,
}

impl LakePromotion {
    pub fn new(
        rocks: Arc<TheoremDb>,
        pg: DatabaseConnection,
        lake: Arc<LakeBuilder>,
        discovery_tx: tokio::sync::broadcast::Sender<DiscoveryEvent>,
    ) -> Self {
        Self {
            rocks,
            pg,
            lake,
            discovery_tx,
            notifiers: Mutex::new(HashMap::new()),
        }
    }

    /// Get-or-create the Notify handle for a theorem_id. Used by both
    /// the drain (to fire wakeups) and synchronous waiters (to park).
    async fn notifier_for(&self, id: TheoremId) -> Arc<Notify> {
        let mut map = self.notifiers.lock().await;
        map.entry(id)
            .or_insert_with(|| Arc::new(Notify::new()))
            .clone()
    }

    /// Synchronous wait helper: enqueue at priority 0 and park up to
    /// `timeout`. Returns the post-promotion VerificationStatus by
    /// re-reading from RocksDB. Used by `lean_download` (P-Task 2) and
    /// `POST /api/theorems/{id}/verify` (P-Task 4).
    pub async fn await_promotion(
        &self,
        id: TheoremId,
        timeout: Duration,
    ) -> Result<Option<nasrudin_core::VerificationStatus>> {
        // Already terminal? Don't enqueue, just return.
        if let Ok(Some(t)) = self.rocks.get_theorem(&id) {
            if Self::is_terminal(&t.verified) {
                return Ok(Some(t.verified));
            }
        }
        let notify = self.notifier_for(id).await;
        // Enqueue at priority 0 (manual / sync trigger).
        let _ = self.rocks.enqueue_lake_promotion(&id, 0);
        // Park on the Notify with timeout.
        let _ = tokio::time::timeout(timeout, notify.notified()).await;
        // Re-read final state.
        Ok(self.rocks.get_theorem(&id).ok().flatten().map(|t| t.verified))
    }

    fn is_terminal(status: &nasrudin_core::VerificationStatus) -> bool {
        matches!(
            status,
            nasrudin_core::VerificationStatus::Verified { tactic_used, .. }
                if tactic_used == "lake_build"
        ) || matches!(
            status,
            nasrudin_core::VerificationStatus::Rejected { .. }
                | nasrudin_core::VerificationStatus::Timeout
        )
    }

    /// Wake every waiter for a theorem and clean up the notifier.
    async fn notify_done(&self, id: &TheoremId) {
        let mut map = self.notifiers.lock().await;
        if let Some(notify) = map.remove(id) {
            notify.notify_waiters();
        }
    }

    /// One drain tick: pull a batch, lake-verify each (concurrent
    /// against the LakeBuilder semaphore), update state.
    async fn drain_once(&self) -> Result<usize> {
        let batch = self.rocks.drain_lake_promotion_batch(BATCH_SIZE)?;
        if batch.is_empty() {
            return Ok(0);
        }
        let processed = batch.len();
        for (queue_key, theorem_id) in batch {
            // Skip if this theorem already reached a terminal state via
            // some other code path (a manual verify and a seed-trigger
            // racing on the same id, for instance). Cheap check; lake
            // build is the expensive thing.
            if let Ok(Some(t)) = self.rocks.get_theorem(&theorem_id) {
                if Self::is_terminal(&t.verified) {
                    self.rocks.ack_lake_promotion(&queue_key).ok();
                    self.notify_done(&theorem_id).await;
                    continue;
                }
            }
            // Fetch lean_source from PG (RocksDB Theorem doesn't carry it).
            let row = match theorem_q::get_by_id(&self.pg, &theorem_id).await {
                Ok(Some(r)) => r,
                _ => {
                    // PG row missing — possibly still in pg_drain queue.
                    // Re-enqueue at priority 1 so we retry next tick.
                    self.rocks.ack_lake_promotion(&queue_key).ok();
                    self.rocks.enqueue_lake_promotion(&theorem_id, 1).ok();
                    continue;
                }
            };
            let theorem_id_hex = hex::encode(theorem_id);
            let outcome = self
                .lake
                .verify(&row.lean_source, &theorem_id_hex)
                .await
                .unwrap_or(VerifyOutcome::Rejected {
                    reason: "lake_promotion_dispatch_error".into(),
                    stderr_tail: String::new(),
                });
            // Capture pre-verify status so we can detect "worker_claim
            // disagreement" — the rare-but-critical case where the
            // worker said `worker_verified=true` (claimed local lake
            // succeeded) but the server's lake build now disagrees.
            // That's a spot-check failure on a high-trust submission
            // and warrants an extra-loud audit trail.
            let was_worker_claim = matches!(
                &row.verification_tactic,
                Some(t) if t == "worker_claim"
            );
            match outcome {
                VerifyOutcome::Verified {
                    tactic,
                    duration_ms,
                } => {
                    self.flip_lake_verified(&row, &tactic, duration_ms).await?;
                    self.record_spot_check(&row, true, was_worker_claim).await;
                }
                VerifyOutcome::Rejected {
                    reason,
                    stderr_tail,
                } => {
                    let full_reason = if was_worker_claim {
                        format!(
                            "worker_claim_disagreement: server_lake_failed: {reason}: {stderr_tail}"
                        )
                    } else {
                        format!("lake_failed: {reason}: {stderr_tail}")
                    };
                    if was_worker_claim {
                        tracing::error!(
                            theorem_id = %hex::encode(&row.id),
                            contributor_id = %row.contributor_id,
                            "worker_claim disagreement: worker submitted with worker_verified=true \
                             but server lake build rejected — cascading + tanking reputation"
                        );
                    }
                    self.flip_rejected_with_cascade(&row, &full_reason).await?;
                    self.record_spot_check(&row, false, was_worker_claim).await;
                }
            }
            // Ack ALL queue entries for this id (across all priority
            // lanes) so a manual verify and a seed-trigger don't both
            // re-fire the lake build for the same id.
            self.rocks.ack_lake_promotion_all(&theorem_id).ok();
            self.notify_done(&theorem_id).await;
        }
        Ok(processed)
    }

    /// PG + RocksDB update for a successful lake promotion. Bumps the
    /// `tactic_used` discriminator from `"chain_replay"` to
    /// `"lake_build"` so the seed handler now considers this row a
    /// legitimate peer-axiom.
    async fn flip_lake_verified(
        &self,
        row: &nasrudin_pg::entity::theorems::Model,
        tactic: &str,
        duration_ms: u32,
    ) -> Result<()> {
        // PG: re-mark with path="lake_promotion", tactic="lake_build".
        let _ = theorem_q::mark_verified(
            &self.pg,
            &row.id,
            "lake_promotion",
            "lake_build",
            duration_ms as i32,
        )
        .await;

        // RocksDB: update Theorem and re-stamp verified_at index.
        let mut id_arr = [0u8; 8];
        if row.id.len() == 8 {
            id_arr.copy_from_slice(&row.id);
            let now_micros = Utc::now().timestamp_micros();
            if let Ok(Some(mut theorem)) = self.rocks.get_theorem(&id_arr) {
                theorem.verified = nasrudin_core::VerificationStatus::Verified {
                    proof_term: Vec::new(),
                    tactic_used: "lake_build".into(),
                };
                let _ = self.rocks.put_theorem(&theorem);
            }
            let _ = self.rocks.mark_verified_at(&id_arr, now_micros);
        }

        let _ = self.discovery_tx.send(DiscoveryEvent::TheoremVerified {
            theorem_id: hex::encode(&row.id),
            verification_path: "lake_promotion".into(),
            duration_ms,
        });

        let _ = tactic;
        Ok(())
    }

    /// Record a spot-check outcome against the worker that submitted
    /// this theorem. Updates the EMA reputation score and the lifetime
    /// pass/fail counters. On `worker_claim` disagreement (worker said
    /// pass, server says fail) we additionally check whether the
    /// reputation has fallen below the auto-revoke threshold and, if
    /// so, revoke the worker.
    ///
    /// `contributor_id` on a theorem row is the worker_id; an empty or
    /// missing contributor_id is the legacy/admin path and gets
    /// silently skipped.
    async fn record_spot_check(
        &self,
        row: &nasrudin_pg::entity::theorems::Model,
        passed: bool,
        was_worker_claim: bool,
    ) {
        let worker_id = row.contributor_id.trim();
        if worker_id.is_empty() || worker_id == "admin" {
            return;
        }
        if let Err(e) = worker_q::record_spot_check(&self.pg, worker_id, passed).await {
            tracing::warn!(
                worker_id = %worker_id,
                "lake_promotion: record_spot_check failed: {e}"
            );
            return;
        }
        if !passed {
            // Auto-revoke heuristic: a worker_claim disagreement is
            // weighty (worker actively claimed local lake passed). If
            // the EMA has decayed below 0.2, revoke. The 0.2 threshold
            // matches the ingest gate in handlers/ingest.rs so a
            // revoked worker can't resubmit anyway.
            if let Ok(Some(score)) = worker_q::get_reputation(&self.pg, worker_id).await {
                if score < 0.2 {
                    let reason = if was_worker_claim {
                        "auto_revoke: worker_claim_disagreement + reputation < 0.2"
                    } else {
                        "auto_revoke: chain_replay lake_failed + reputation < 0.2"
                    };
                    let _ = worker_q::auto_revoke(&self.pg, worker_id, reason).await;
                }
            }
        }
    }

    /// Lake-failure path: mark the theorem Rejected and cascade the
    /// rejection to every descendant via the lineage graph (P-Task 3).
    /// Each cascaded id also fires a TheoremRejected SSE event.
    async fn flip_rejected_with_cascade(
        &self,
        row: &nasrudin_pg::entity::theorems::Model,
        reason: &str,
    ) -> Result<()> {
        // PG mirror update for the root.
        let _ = theorem_q::mark_rejected(&self.pg, &row.id, reason).await;

        // RocksDB cascade walk over CF_LINEAGE.
        let mut id_arr = [0u8; 8];
        if row.id.len() == 8 {
            id_arr.copy_from_slice(&row.id);
            let cascaded = match self.rocks.cascade_reject(id_arr, reason) {
                Ok(ids) => ids,
                Err(e) => {
                    tracing::error!(
                        theorem_id = %hex::encode(&row.id),
                        "lake_promotion: cascade_reject failed: {e}"
                    );
                    Vec::new()
                }
            };

            // PG-mirror the cascade. mark_rejected_batch is a single
            // UPDATE so a fanout of 1000 descendants is one PG round-trip.
            if !cascaded.is_empty() {
                let descendant_bytes: Vec<Vec<u8>> = cascaded
                    .iter()
                    .filter(|d| **d != id_arr)
                    .map(|d| d.to_vec())
                    .collect();
                if !descendant_bytes.is_empty() {
                    let cascade_reason = format!("ancestor_rejected: {}", hex::encode(id_arr));
                    let _ = theorem_q::mark_rejected_batch(
                        &self.pg,
                        &descendant_bytes,
                        &cascade_reason,
                    )
                    .await;
                }
            }

            // SSE: one TheoremRejected per cascaded id.
            for cid in &cascaded {
                let cid_hex = hex::encode(cid);
                let local_reason = if *cid == id_arr {
                    reason.to_string()
                } else {
                    format!("ancestor_rejected: {}", hex::encode(id_arr))
                };
                let _ = self.discovery_tx.send(DiscoveryEvent::TheoremRejected {
                    theorem_id: cid_hex,
                    reason: local_reason,
                });
                // Wake any synchronous waiters on cascaded ids.
                self.notify_done(cid).await;
            }
            tracing::warn!(
                theorem_id = %hex::encode(&row.id),
                cascaded = cascaded.len(),
                "lake_promotion: rejected with cascade"
            );
        }
        Ok(())
    }
}

/// Spawn the drain loop. Runs forever. Cancel by dropping the API.
pub async fn drain_loop(promotion: Arc<LakePromotion>) {
    if let Ok(depth) = promotion.rocks.lake_promotion_queue_depth() {
        if depth > 0 {
            tracing::info!(
                "lake_promotion: drain loop starting with {depth} queued promotions"
            );
        }
    }
    loop {
        tokio::time::sleep(DRAIN_INTERVAL).await;
        if let Err(e) = promotion.drain_once().await {
            tracing::warn!("lake_promotion: drain tick failed: {e}");
        }
    }
}

/// Background crawler: every CRAWLER_INTERVAL, walk CF_THEOREMS and
/// enqueue any non-`lake_build` Verified row at priority 2. Ensures
/// eventual server-side kernel confirmation of every theorem
/// regardless of consumption — this is the defense-in-depth path the
/// user flagged: "if something is already lazily verified and then
/// suddenly appears in the front of the queue despite just being
/// verified then obviously then verify it again". `worker_claim` rows
/// are propagated to peers immediately (per seed.rs) but the crawler
/// guarantees they all eventually pass the server's own lake build.
pub async fn crawler_loop(promotion: Arc<LakePromotion>) {
    loop {
        tokio::time::sleep(CRAWLER_INTERVAL).await;
        let rocks = Arc::clone(&promotion.rocks);
        let enqueued = tokio::task::spawn_blocking(move || -> Result<usize> {
            let mut count = 0usize;
            for theorem in rocks.list_theorems()?.into_iter().take(CRAWLER_BATCH) {
                if let nasrudin_core::VerificationStatus::Verified { tactic_used, .. } =
                    &theorem.verified
                {
                    if tactic_used == "chain_replay" || tactic_used == "worker_claim" {
                        rocks.enqueue_lake_promotion(&theorem.id, 2).ok();
                        count += 1;
                    }
                }
            }
            Ok(count)
        })
        .await
        .ok()
        .and_then(|r| r.ok())
        .unwrap_or(0);
        if enqueued > 0 {
            tracing::info!(
                "lake_promotion: background crawler enqueued {enqueued} ChainVerified rows"
            );
        }
    }
}
