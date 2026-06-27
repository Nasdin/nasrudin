//! Run a single paid Researcher GA slice for one claimed conjecture.
//!
//! Lifecycle (paired with `paid_jobs_client::PaidJobsClient`):
//!  1. Caller `PaidJobsClient::claim()`s a job → `PaidJob`.
//!  2. Caller invokes `run_paid_slice(...)` — this function.
//!  3. We compile the user's hunch (LaTeX) → Expr → AC-canonical hash
//!     once at the start of the slice. That hash is the success
//!     criterion: a verified theorem matches the conjecture iff its
//!     `final_expr`'s AC-canonical hash equals the hunch's. The match
//!     is tolerant of trivial restatements (commutativity, associativity,
//!     identity simplifications) because `canonical_ac_hash` is the
//!     same canonical form the rest of the platform uses for dedup.
//!  4. We loop short `run_discovery` chunks (a few generations each),
//!     heartbeating every 30 s with the actual progress counters and
//!     the slot-hours debited since the last heartbeat.
//!  5. On a verified theorem whose hash matches, call `mark_proved` and
//!     end the slice. Theorems verified during the slice that *don't*
//!     match the conjecture get logged but not marked — they're still
//!     useful corpus growth (the chain_engine submission path picks
//!     them up via the worker's normal /api/ingest flow elsewhere).
//!  6. When the server reports `continue: false` (budget exhausted),
//!     or wallclock hits 24 h, the slice ends. On any error before
//!     that, we attempt a `release` so another worker can pick up the
//!     job within seconds instead of waiting for the lease reaper.
//!
//! When the hunch fails to parse as LaTeX (e.g. a free-form English
//! sentence), we fall back to "first verified theorem in the slice
//! is treated as the proof" — same as v1. This keeps the runner
//! useful for hunches even before the parser stack supports plain
//! English. The fallback is logged at WARN so ops can see when it
//! kicks in.
//!
//! Conjecture-relative AxiomStore subsetting:
//!  * If the hunch parses as LaTeX, we walk it to collect every Var
//!    identifier (e.g. `{E, m, c}`).
//!  * The slice's effective AxiomStore is filtered to keep only
//!    axioms whose canonical statement mentions at least one of those
//!    identifiers, plus a fixed "core kept always" set (sign /
//!    non-negativity / classical mechanics postulates) so chains can
//!    still close on standard physics priors.
//!  * Empty intersection (e.g. hunch with no Var identifiers, or no
//!    matching axioms) → keep the full store as a safe fallback.
//!
//! Slot-hour accounting honors the per-job allocated slot count:
//!  * Server-side: `conjecture_jobs.allocated_slots` is set on
//!    /api/jobs/claim from the worker's `available_lake_slots`.
//!  * Worker-side: `PaidJob.allocated_slots` (defaulting to 4 for
//!    backwards-compat with existing rows) is consumed here for the
//!    consumed_h_unsent debit math.
//!
//! Heartbeat cadence is hard-coded to 30 s.

use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::Result;
use rand::SeedableRng;
use rand::rngs::StdRng;
use uuid::Uuid;

use nasrudin_derive::AxiomStore;

use crate::chain_engine::{DiscoveryConfig, DiscoveryReport, run_discovery};
use crate::paid_jobs_client::{HeartbeatBody, MarkProvedBody, PaidJob, PaidJobsClient};
use crate::steering_knobs::apply_steering_knobs_for_domain;

/// Heartbeat cadence — 30 s aligns with the server's 5-minute lease
/// (10 heartbeats per lease window provides plenty of jitter
/// tolerance for slow networks).
const HEARTBEAT_INTERVAL: Duration = Duration::from_secs(30);

/// Default slot allocation per paid job, used when `PaidJob.allocated_slots`
/// is missing (server pre-elastic-sizing or a backwards-compat row).
/// Matches the 96 slot-hour quota = 4 slots × 24 h.
pub const DEFAULT_SLOTS_PER_JOB: f32 = 4.0;

/// Backwards-compat alias kept for pinning callers; new code should
/// use the per-job `allocated_slots` from `PaidJob`.
pub const SLOTS_PER_JOB: f32 = DEFAULT_SLOTS_PER_JOB;

/// Always-keep axiom names: every paid slice retains these regardless
/// of the conjecture's identifier set, because chain-replay almost
/// always needs sign + non-negativity priors and the classical-
/// mechanics postulate set is small and broadly useful.
const ALWAYS_KEEP_AXIOMS: &[&str] = &[
    // SR sign axioms (registered by load_special_relativity_upstream).
    "c_positive",
    "mass_nonneg",
    "energy_nonneg",
    // Classical mechanics postulates — kinematic primitives.
    // Names mirror nasrudin_derive::postulates_classical.
    "newton_second_law",
    "momentum_definition",
    "kinetic_energy_definition",
    "work_definition",
];

/// Per-chunk generation count. Small chunks keep heartbeat granularity
/// high without GA overhead. Dropped from 10 → 3 in v0.2.1 because
/// the elaborator-backed Lean verify per candidate can take many
/// minutes on a worst-case nlinarith search; with 10 gens a single
/// slow chain stalled the inline heartbeat past the lease window
/// and the server reaper released the job back to queued. Worker
/// kept grinding with a stale lease but no progress was visible
/// server-side. 3 gens × 32 pop ≈ 96 candidates per chunk = ~0.3 s
/// best case, leaves plenty of room for one slow chain inside the
/// 30-min lease window (raised from 5 min on the server side in the
/// same release). See task #41.
const GENS_PER_CHUNK: usize = 3;

/// Walk an `Expr` and collect every `Var(name)`. Used by the axiom-
/// subsetting pass to find which identifiers the user's hunch
/// mentions.
fn collect_vars(expr: &nasrudin_core::Expr, out: &mut std::collections::HashSet<String>) {
    use nasrudin_core::Expr;
    match expr {
        Expr::Var(name) => {
            out.insert(name.clone());
        }
        Expr::App(f, x) => {
            collect_vars(f, out);
            collect_vars(x, out);
        }
        Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) | Expr::Let(_, ty, body) => {
            collect_vars(ty, out);
            collect_vars(body, out);
        }
        Expr::BinOp(_, a, b) => {
            collect_vars(a, out);
            collect_vars(b, out);
        }
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => {
            collect_vars(e, out);
        }
        Expr::Sum {
            body, lower, upper, ..
        }
        | Expr::Prod {
            body, lower, upper, ..
        } => {
            collect_vars(body, out);
            collect_vars(lower, out);
            collect_vars(upper, out);
        }
        Expr::Integral {
            body, lower, upper, ..
        } => {
            collect_vars(body, out);
            if let Some(l) = lower {
                collect_vars(l, out);
            }
            if let Some(u) = upper {
                collect_vars(u, out);
            }
        }
        Expr::Limit {
            body, approaching, ..
        } => {
            collect_vars(body, out);
            collect_vars(approaching, out);
        }
        Expr::Lit(_, _) | Expr::Const(_) => {}
    }
}

/// Build a restricted `AxiomStore` containing only axioms whose
/// canonical-form mentions at least one identifier from
/// `wanted_idents`, plus the `ALWAYS_KEEP_AXIOMS` core. Returns the
/// full store unchanged when `wanted_idents` is empty or the
/// intersection is too small to be useful (< 4 axioms).
fn subset_store_for_hunch(
    full: &AxiomStore,
    wanted_idents: &std::collections::HashSet<String>,
) -> AxiomStore {
    if wanted_idents.is_empty() {
        return full.clone();
    }
    let always: std::collections::HashSet<&str> = ALWAYS_KEEP_AXIOMS.iter().copied().collect();
    let mut out = AxiomStore::new();
    let mut kept = 0usize;
    // `full.iter()` walks both hot and cold tiers. The cold half is
    // ~195k entries; we walk it once at paid-slice init to subset
    // down to the hunch-relevant axioms (typically <100 kept), then
    // the resulting store is hot-only and the GA's hot path runs
    // free of any RocksDB lookup. Acceptable cost for the
    // hunch-narrowing stage.
    for ax in full.iter() {
        let always_keep = always.contains(ax.name.as_str());
        let mentions = {
            let canon = ax.statement.to_canonical();
            wanted_idents
                .iter()
                .any(|ident| canon.contains(&format!("v:{ident}")))
        };
        if always_keep || mentions {
            out.register(ax);
            kept += 1;
        }
    }
    if kept < 4 {
        // Subsetting was too aggressive (e.g. exotic identifiers in
        // the hunch don't appear in any axiom). Fall back to the full
        // store rather than starve the GA.
        return full.clone();
    }
    out
}

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

    // Compile the hunch into the AC-canonical hash we'll match
    // against. None = parser couldn't make sense of the hunch (free-
    // form English, exotic notation, etc.) — fall back to v1 "first
    // verified theorem is the proof" semantics so the slice still
    // produces *something* for the user.
    //
    // While we're at it, walk the parsed Expr to collect the variable
    // identifiers — feeds the axiom-subsetting pass below.
    let mut wanted_idents: std::collections::HashSet<String> = Default::default();
    let target_hash: Option<[u8; 8]> = match nasrudin_core::parse::parse_latex(job.hunch.trim()) {
        Ok(expr) => {
            collect_vars(&expr, &mut wanted_idents);
            let h = nasrudin_core::canonical_ac_hash(&expr);
            tracing::info!(
                %job_id,
                target_hash = hex::encode(h),
                idents = ?wanted_idents,
                "paid slice target compiled from hunch"
            );
            Some(h)
        }
        Err(e) => {
            tracing::warn!(
                %job_id,
                error = %e,
                hunch = job.hunch.chars().take(80).collect::<String>(),
                "paid slice could not parse hunch as LaTeX; falling back to first-verified semantics"
            );
            None
        }
    };

    // Conjecture-relative axiom subsetting: if we extracted identifiers
    // from the hunch, narrow the GA's AxiomStore to axioms whose
    // canonical statement mentions any of them (plus the always-keep
    // core). Empty/exotic identifier sets fall back to the full store.
    let scoped_store = subset_store_for_hunch(&store, &wanted_idents);
    let scoped_store = Arc::new(scoped_store);
    let original_size = store.iter().count();
    let scoped_size = scoped_store.iter().count();
    if wanted_idents.len() > 0 && scoped_size < original_size {
        tracing::info!(
            %job_id,
            full = original_size,
            scoped = scoped_size,
            "paid slice scoped AxiomStore from hunch identifiers"
        );
    }

    // Slot-hour accounting honors the per-job allocation. Falls back
    // to DEFAULT_SLOTS_PER_JOB for backwards-compat with rows the
    // server hasn't stamped yet.
    let slot_count: f32 = job
        .allocated_slots
        .map(|s| s as f32)
        .unwrap_or(DEFAULT_SLOTS_PER_JOB)
        .max(1.0);

    // Per-job steering payload — set by the researcher at submit
    // time or by the platform target seeder. Shape matches the
    // LLM-emitted cluster payload's `config.*`, so we wrap it in
    // `{ "config": <seed> }` before handing to apply_steering_knobs
    // (which expects to find knobs under `.config`).
    let steering_wrapper: Option<serde_json::Value> = job
        .seed
        .as_ref()
        .map(|s| serde_json::json!({ "config": s }));
    let steering_domain_key: &str = job.domain_hint.as_deref().unwrap_or("");

    tracing::info!(
        %job_id,
        hunch = job.hunch.chars().take(80).collect::<String>(),
        remaining_h = job.lake_slot_hours_remaining,
        target_compiled = target_hash.is_some(),
        steered = steering_wrapper.is_some(),
        slot_count,
        "starting paid GA slice"
    );

    // Fast path: when the hunch parses cleanly to a canonical_ac_hash
    // that ALREADY exists in the corpus, mark_proved immediately
    // instead of burning the budget re-deriving a known theorem.
    // Closes the gap where researcher hunches like "E = m * c^2"
    // would loop forever even though the seed-elite proof has been
    // in the corpus since gen 0. Best-effort: any lookup error
    // falls through to the normal GA slice (no regression).
    if let Some(target) = target_hash {
        let hex_hash = hex::encode(target);
        match client.lookup_by_ac_hash(&hex_hash).await {
            Ok(Some(theorem_id_hex)) => {
                tracing::info!(
                    %job_id,
                    theorem_id_hex,
                    "paid slice fast-path: target canonical already in corpus, marking proved without GA work"
                );
                if let Err(e) = client
                    .mark_proved(
                        job_id,
                        &MarkProvedBody {
                            theorem_id_hex: theorem_id_hex.clone(),
                            statement_latex: Some(job.hunch.clone()),
                        },
                    )
                    .await
                {
                    tracing::warn!(%job_id, error = %e, "fast-path mark_proved failed; falling through to GA slice");
                } else {
                    return Ok(());
                }
            }
            Ok(None) => {
                // Hunch is novel — proceed with the GA slice as normal.
            }
            Err(e) => {
                tracing::debug!(%job_id, error = %e, "by_ac_hash lookup failed; proceeding with GA slice");
            }
        }
    }

    loop {
        // Run one short chunk under the slice's config.
        let mut chunk_cfg = base_config.clone();
        chunk_cfg.generations = GENS_PER_CHUNK;
        // Apply per-job steering on top of the base config every
        // chunk (cheap; idempotent under clamping). Researcher-
        // supplied knobs override anything the live cluster steerer
        // would inject — paying users get explicit priority over
        // automatic LLM bias.
        if let Some(s) = steering_wrapper.as_ref() {
            apply_steering_knobs_for_domain(&mut chunk_cfg, s, steering_domain_key);
        }
        let report: DiscoveryReport = run_discovery(&scoped_store, &chunk_cfg, &mut rng);
        cum_attempted += report.total_candidates as i32;
        cum_verified += report.verified.len() as i32;

        // Look for a verified theorem whose AC-canonical hash matches
        // the conjecture target. With `target_hash = None` (parse
        // fallback) the first verified theorem wins.
        let matched = report.verified.iter().find(|d| match target_hash {
            Some(target) => nasrudin_core::canonical_ac_hash(&d.final_expr) == target,
            None => true,
        });
        if let Some(d) = matched {
            let id_bytes = nasrudin_core::canonical_hash(&d.canonical);
            let theorem_id_hex = hex::encode(id_bytes);
            tracing::info!(
                %job_id,
                theorem_id_hex,
                matched_target = target_hash.is_some(),
                "paid slice produced matching theorem; marking proved"
            );
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
        // Verified theorems that didn't match the target are NOT
        // marked-proved — they're still useful corpus growth and
        // get submitted via the worker's normal /api/ingest flow
        // (chain_engine produces the submission elsewhere).
        if !report.verified.is_empty() && target_hash.is_some() {
            tracing::debug!(
                %job_id,
                non_matching = report.verified.len(),
                "paid slice verified theorems didn't match target; continuing"
            );
        }

        // Accumulate slot-hours since the last heartbeat. We send the
        // delta (consumed_h_unsent) on the next tick; the server clamps
        // it server-side against the wallclock to defeat lying workers.
        let chunk_elapsed = last_heartbeat.elapsed().as_secs_f32();
        consumed_h_unsent += (chunk_elapsed / 3600.0) * slot_count;

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
