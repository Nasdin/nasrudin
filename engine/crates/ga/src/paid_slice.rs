//! Run a single paid Researcher GA slice for one claimed conjecture.
//!
//! Lifecycle (paired with `paid_jobs_client::PaidJobsClient`):
//!  1. Caller `PaidJobsClient::claim()`s a job → `PaidJob`.
//!  2. Caller invokes `run_paid_slice(...)` — this function.
//!  3. We loop short `run_discovery` chunks (a few generations each),
//!     heartbeating every 30 s with the actual progress counters and
//!     the slot-hours debited since the last heartbeat.
//!  4. On any verified theorem we synchronously call `mark_proved`
//!     (the conjecture target's exact symbolic form is hard to compile
//!     from natural-language hunches — for v1 we treat the first
//!     verified theorem in the slice as the proof; v2 will pin a
//!     compiled `TargetSpec` and only mark on canonical-hash match).
//!  5. When the server reports `continue: false` (budget exhausted),
//!     or wallclock hits 24 h, the slice ends. On any error before
//!     that, we attempt a `release` so another worker can pick up the
//!     job within seconds instead of waiting for the lease reaper.
//!
//! v1 simplifications:
//!  * Every slice gets the worker's whole AxiomStore + classical
//!    mechanics postulates. No conjecture-specific axiom subsetting.
//!  * `target_shape` matching is left to v2 (LaTeX → Expr compiler).
//!  * Slot-hour accounting uses `(elapsed_seconds / 3600) * slot_count`
//!    where `slot_count = 4` (matches the 96 slot-hour quota = 4 × 24h).
//!  * Heartbeat cadence is hard-coded to 30 s.

use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::Result;
use rand::SeedableRng;
use rand::rngs::StdRng;
use uuid::Uuid;

use nasrudin_derive::AxiomStore;

use crate::chain_engine::{run_discovery, DiscoveryConfig, DiscoveryReport};
use crate::paid_jobs_client::{
    HeartbeatBody, MarkProvedBody, PaidJob, PaidJobsClient,
};

/// Heartbeat cadence — 30 s aligns with the server's 5-minute lease
/// (10 heartbeats per lease window provides plenty of jitter
/// tolerance for slow networks).
const HEARTBEAT_INTERVAL: Duration = Duration::from_secs(30);

/// v1 fixed slot allocation per paid job. Matches the 96 slot-hour
/// quota = 4 slots × 24 h. The server uses the same constant on the
/// claim path; both must move together when v2 introduces elastic
/// per-job sizing.
pub const SLOTS_PER_JOB: f32 = 4.0;

/// Per-chunk generation count. Small chunks keep heartbeat granularity
/// high without GA overhead (each chunk is ~few seconds of work on a
/// 32-pop, 10-gen chunk).
const GENS_PER_CHUNK: usize = 10;

/// Run a paid slice end-to-end. Returns `Ok(())` for both proved and
/// budget-exhausted endings — those are normal terminal states. `Err`
/// is reserved for transport failures the caller should escalate.
pub async fn run_paid_slice(
    client: &PaidJobsClient,
    job: &PaidJob,
    store: Arc<AxiomStore>,
    base_config: DiscoveryConfig,
) -> Result<()> {
    let job_id = job.job_id;
    let started = Instant::now();
    let mut last_heartbeat = started;
    // RNG seeded from the job_id so a re-claim of the same job after a
    // worker death produces the same exploration trajectory — easier
    // post-hoc reproduction.
    let mut rng = StdRng::seed_from_u64(seed_from_uuid(job_id));

    let mut cum_attempted: i32 = 0;
    let mut cum_verified: i32 = 0;
    let mut consumed_h_unsent: f32 = 0.0;

    tracing::info!(
        %job_id,
        hunch = job.hunch.chars().take(80).collect::<String>(),
        remaining_h = job.lake_slot_hours_remaining,
        "starting paid GA slice"
    );

    loop {
        // Run one short chunk under the slice's config.
        let mut chunk_cfg = base_config.clone();
        chunk_cfg.generations = GENS_PER_CHUNK;
        let report: DiscoveryReport = run_discovery(&store, &chunk_cfg, &mut rng);
        cum_attempted += report.total_candidates as i32;
        cum_verified += report.verified.len() as i32;

        // mark_proved on the first kernel-verified discovery in this
        // chunk. The theorem id used by the API is the canonical-hash
        // bytes hex-encoded — see `theorem_id_from_canonical`.
        if let Some(d) = report.verified.first() {
            let id_bytes =
                nasrudin_core::canonical_hash(&d.canonical);
            let theorem_id_hex = hex::encode(id_bytes);
            tracing::info!(%job_id, theorem_id_hex, "paid slice produced verified theorem; marking proved");
            // Best-effort: a 4xx here usually means another worker
            // raced us to the same job — let the slice exit gracefully.
            if let Err(e) = client
                .mark_proved(
                    job_id,
                    &MarkProvedBody {
                        theorem_id_hex: theorem_id_hex.clone(),
                        statement_latex: Some(d.canonical.clone()),
                    },
                )
                .await
            {
                tracing::warn!(%job_id, error = %e, "mark_proved failed");
            }
            return Ok(());
        }

        // Accumulate slot-hours since the last heartbeat. We send the
        // delta (consumed_h_unsent) on the next tick; the server clamps
        // it server-side against the wallclock to defeat lying workers.
        let chunk_elapsed = last_heartbeat.elapsed().as_secs_f32();
        consumed_h_unsent += (chunk_elapsed / 3600.0) * SLOTS_PER_JOB;

        // Heartbeat at the cadence boundary (or every chunk if the
        // chunk took longer than the cadence — unlikely but cheap).
        if last_heartbeat.elapsed() >= HEARTBEAT_INTERVAL {
            let body = HeartbeatBody {
                candidates_attempted_delta: cum_attempted,
                candidates_verified_delta: cum_verified,
                lake_slot_hours_consumed_delta: consumed_h_unsent,
                current_best_fitness: 0.0,
                current_best_chain_length: 0,
            };
            match client.heartbeat(job_id, &body).await {
                Ok(resp) => {
                    cum_attempted = 0;
                    cum_verified = 0;
                    consumed_h_unsent = 0.0;
                    last_heartbeat = Instant::now();
                    if !resp.continue_ {
                        tracing::info!(
                            %job_id,
                            reason = resp.reason.as_deref().unwrap_or("budget_exhausted"),
                            "paid slice ended (server signal)"
                        );
                        return Ok(());
                    }
                }
                Err(e) => {
                    // Network blip: keep grinding, accumulate the
                    // delta, retry on the next tick. If the lease
                    // expires the reaper picks the job up.
                    tracing::warn!(%job_id, error = %e, "heartbeat failed; retrying next tick");
                }
            }
        }

        // 24 h hard wallclock cap (mirrors the budget-spec wall_seconds=86400).
        if started.elapsed() > Duration::from_secs(86_400) {
            tracing::info!(%job_id, "paid slice hit 24 h wallclock cap; releasing");
            let _ = client.release(job_id).await;
            return Ok(());
        }
    }
}

fn seed_from_uuid(id: Uuid) -> u64 {
    // First 8 bytes of the UUID make a perfectly fine RNG seed.
    let bytes = id.as_bytes();
    u64::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ])
}
