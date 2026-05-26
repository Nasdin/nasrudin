//! Platform-owned conjecture targets.
//!
//! When no paying researcher is steering the cluster, the workers
//! shouldn't fall back to pure-random GA — that wastes compute on
//! candidates with effectively zero chance of being meaningful.
//! Instead, the platform itself seeds a small set of "we are
//! hunting for these headlines" conjecture_jobs rows at boot. These
//! sit in the same queue paying researcher jobs use, but at a lower
//! `slice_priority` (3 vs 5/6), so:
//!
//!  * If there's a paying researcher job queued → worker claims it
//!    first (the researcher tier always wins).
//!  * Otherwise → worker claims a platform target (E=mc², F=ma, ...).
//!    The same `paid_slice` infrastructure runs the directed hunt,
//!    using curated `seed` steering tuned for each headline.
//!  * Only when both queues are empty does the worker drop to its
//!    legacy random-GA loop.
//!
//! Why one table instead of two: the claim/heartbeat/cancel/lease
//! infrastructure is already production-hardened. Forking it would
//! duplicate the lease reaper, the slot accounting, the SSE event
//! topology, and the refund logic — all for a row that's
//! semantically just "an unpaid research job owned by the
//! platform." Sharing the table costs us one `tier` column filter
//! in researcher-facing endpoints (already in place) and a
//! sentinel `owner_id`.
//!
//! Sentinel owner: a fixed UUID with no real user account. The
//! refund query is owner-gated and tier-gated so platform jobs are
//! invisible to `cancel_paid_with_refund`. The user list / detail
//! endpoints filter by `tier = 'researcher'` so platform rows
//! never appear in the user's job listing either.

use nasrudin_pg::sea_orm::{
    ActiveModelTrait, ColumnTrait, DatabaseConnection, EntityTrait, QueryFilter, Set,
};
use serde_json::{json, Value};
use tracing::{info, warn};
use uuid::Uuid;

/// Sentinel owner UUID for platform-owned conjecture rows. Stable
/// across restarts so the boot-time upsert is idempotent. Never
/// has a corresponding `users` row created — the FK is dropped /
/// not enforced for this row by the schema (see migration
/// `m20260520_000050_platform_owner_sentinel.rs` — TODO if FK
/// blocks us at boot).
pub const PLATFORM_OWNER_ID: Uuid = Uuid::from_u128(0x0000_0000_0000_0000_0000_0000_0000_0001);

/// Priority for platform-tier rows. Below the researcher baseline
/// (5) so paying users always preempt; above the queue floor so
/// platform work still happens when no researchers are active.
const PLATFORM_PRIORITY: i32 = 3;

/// Quota stamp per platform row. Generous — these jobs never expire;
/// they're meant to live in the queue until the headline is found.
const PLATFORM_QUOTA_HOURS: i32 = 96 * 1000;

/// One platform target. Mirrors `featured.rs::TargetFormula` but
/// with the snake-case `domain_key` workers expect for atom_pool
/// lookups, and an optional curated `steering` blob.
struct PlatformTarget {
    /// Human-readable hunch — same shape as researcher-submitted
    /// LaTeX (parsed by `nasrudin_core::parse::parse_latex` in
    /// `paid_slice::run_paid_slice`).
    hunch: &'static str,
    /// Domain key consumed by `apply_steering_knobs_for_domain` for
    /// per-domain atom_pool lookup. Snake-case match for the LLM
    /// steerer's emitted keys.
    domain_key: &'static str,
    /// Curated steering payload — atom_pool weights tuned for this
    /// headline. None = use the live cluster steerer snapshot
    /// instead (worker's normal path).
    steering: Option<Value>,
}

/// Hard-coded platform target set. Mirrors `featured.rs::TARGET_FORMULAS`.
/// Curated steering is currently provided for E=mc² (the immediate
/// goal); other headlines fall through to the LLM cluster steerer.
fn platform_targets() -> Vec<PlatformTarget> {
    vec![
        PlatformTarget {
            hunch: "E = m * c^2",
            domain_key: "special_relativity",
            steering: Some(json!({
                // Tilt the GA toward the rest-energy compound. The
                // atom names match `PHYSICS_ATOM_NAMES` in
                // crates/ga/src/chain_ga.rs — the `m_c_sq` weight
                // dominates so `append_productive_suffix` keeps
                // proposing the right-hand side of E=mc² as a
                // candidate compound.
                "atom_pool": {
                    "special_relativity": [
                        { "name": "m_c_sq", "weight": 4.0 },
                        { "name": "c_sq",   "weight": 2.0 },
                        { "name": "m_c",    "weight": 1.0 },
                    ]
                },
                // Bias mutation toward operators that compose
                // upstream postulates into the headline shape.
                "mutation_priors": {
                    "append_productive_suffix": 2.0,
                    "rearrange_equation": 1.5,
                    "substitute_value": 1.3,
                    "insert_random": 0.5,
                },
                "mutation_knobs": {
                    "rate": 0.18,
                    "population_size": 64,
                    "suffix_bias": 0.7,
                    "elitism_fraction": 0.1
                }
            })),
        },
        PlatformTarget {
            hunch: "F = m * a",
            domain_key: "classical_mechanics",
            steering: None,
        },
        PlatformTarget {
            hunch: "S = k_B * ln(Omega)",
            domain_key: "thermodynamics",
            steering: None,
        },
        PlatformTarget {
            // Schrödinger — keep simple LHS so the parser accepts it;
            // canonical-hash matching is what counts at slice time.
            hunch: "i * hbar * d_psi_dt = H * psi",
            domain_key: "quantum_mechanics",
            steering: None,
        },
        PlatformTarget {
            hunch: "R_uv - (1/2) * g_uv * R = 8 * pi * T_uv",
            domain_key: "general_relativity",
            steering: None,
        },
        PlatformTarget {
            hunch: "div_E = rho / epsilon_0",
            domain_key: "electromagnetism",
            steering: None,
        },
    ]
}

/// Ensure the sentinel users row exists. conjecture_jobs.owner_id
/// has an FK to users.id with CASCADE, so we need a real row at
/// the sentinel UUID before any platform conjecture insert can
/// succeed. The row is never auth'd against — it has an empty
/// firebase_uid, no Stripe binding, no credits, and is_admin=false.
/// `ON CONFLICT DO NOTHING` so we don't clobber any field if an
/// earlier boot already inserted it.
async fn ensure_sentinel_user(pg: &DatabaseConnection) -> Result<(), nasrudin_pg::sea_orm::DbErr> {
    use nasrudin_pg::sea_orm::{DatabaseBackend, Statement};
    let stmt = Statement::from_sql_and_values(
        DatabaseBackend::Postgres,
        r#"
        INSERT INTO users (
            id, email, display_name, created_at, plan_tier,
            research_credits, firebase_uid, is_admin, is_trusted
        )
        VALUES (
            $1, 'platform@nasrudin.org', 'Nasrudin Platform', NOW(),
            'platform', 0, 'platform-sentinel', false, false
        )
        ON CONFLICT (id) DO NOTHING
        "#,
        [PLATFORM_OWNER_ID.into()],
    );
    nasrudin_pg::sea_orm::ConnectionTrait::execute_raw(pg, stmt)
        .await
        .map(|_| ())
}

/// Ensure every platform target has at least one open conjecture_jobs
/// row. Idempotent: skips targets that already have a queued/claimed/
/// running row (matched by hunch + tier='platform'). Logs how many
/// rows were inserted vs skipped.
pub async fn ensure_platform_targets(pg: &DatabaseConnection) {
    use nasrudin_pg::entity::conjecture_jobs;
    if let Err(e) = ensure_sentinel_user(pg).await {
        warn!(error = %e, "could not upsert platform sentinel user; platform targets disabled");
        return;
    }
    let targets = platform_targets();
    let mut inserted = 0usize;
    let mut skipped = 0usize;

    for target in targets {
        // Existence check: any non-terminal platform row for this
        // hunch counts as "already enqueued." Terminal rows (proved /
        // budget_exhausted / cancelled) mean the hunt was completed
        // or abandoned and we DON'T re-enqueue automatically — that's
        // the steerer-proposed-target path's job.
        let existing = conjecture_jobs::Entity::find()
            .filter(conjecture_jobs::Column::Tier.eq("platform"))
            .filter(conjecture_jobs::Column::Hunch.eq(target.hunch))
            .filter(
                conjecture_jobs::Column::State
                    .is_in(["queued", "claimed", "running"]),
            )
            .one(pg)
            .await;
        match existing {
            Ok(Some(_)) => {
                skipped += 1;
                continue;
            }
            Ok(None) => {}
            Err(e) => {
                warn!(error = %e, hunch = target.hunch, "platform target existence check failed; skipping");
                continue;
            }
        }

        let am = conjecture_jobs::ActiveModel {
            id: Set(Uuid::new_v4()),
            owner_id: Set(PLATFORM_OWNER_ID),
            state: Set("queued".into()),
            outcome: Set(None),
            hunch: Set(target.hunch.into()),
            domain_hint: Set(Some(target.domain_key.into())),
            provider: Set("platform".into()),
            model: Set("platform_seed".into()),
            suggestions: Set(None),
            chosen_index: Set(None),
            seed: Set(target.steering.clone()),
            budget: Set(json!({
                "wall_seconds": 86_400_000_i64,
                "max_candidates": 100_000_000_i64,
            })),
            claimed_by: Set(None),
            claimed_at: Set(None),
            lease_expires_at: Set(None),
            last_heartbeat_at: Set(None),
            candidates_attempted: Set(0),
            candidates_verified: Set(0),
            verified_theorem_ids: Set(None),
            created_at: Set(chrono::Utc::now().into()),
            completed_at: Set(None),
            paper_draft: Set(None),
            lake_slot_hours_quota: Set(PLATFORM_QUOTA_HOURS),
            lake_slot_hours_consumed: Set(0.0),
            slice_priority: Set(PLATFORM_PRIORITY),
            tier: Set("platform".into()),
            allocated_slots: Set(4),
        };
        match am.insert(pg).await {
            Ok(_) => {
                inserted += 1;
                info!(
                    hunch = target.hunch,
                    domain = target.domain_key,
                    steered = target.steering.is_some(),
                    "platform target enqueued"
                );
            }
            Err(e) => {
                warn!(error = %e, hunch = target.hunch, "platform target insert failed");
            }
        }
    }
    info!(inserted, skipped, "platform target seeding complete");
}

#[cfg(test)]
mod tests {
    use super::platform_targets;

    /// Every platform target must parse as LaTeX (or the equivalent
    /// math-mode shorthand `nasrudin_core::parse::parse_latex`
    /// accepts), otherwise `paid_slice::run_paid_slice` will silently
    /// fall back to "first verified theorem wins" — a directed hunt
    /// with no target check is just slow random GA wearing a hat.
    #[test]
    fn every_platform_target_hunch_parses() {
        for t in platform_targets() {
            let parsed = nasrudin_core::parse::parse_latex(t.hunch);
            assert!(
                parsed.is_ok(),
                "platform target hunch failed to parse: `{}` (domain={}) — err: {:?}",
                t.hunch,
                t.domain_key,
                parsed.err(),
            );
        }
    }

    /// Targets whose `steering` is set must declare an atom_pool keyed
    /// by their own `domain_key` — otherwise the apply_steering_knobs
    /// extractor won't find the pool slice and the atom hints are
    /// silently ignored. Defensive against future copy-paste mistakes.
    #[test]
    fn steered_targets_use_their_own_domain_key() {
        for t in platform_targets() {
            let Some(steering) = t.steering.as_ref() else {
                continue;
            };
            let Some(pool) = steering.get("atom_pool") else {
                continue;
            };
            let key = t.domain_key;
            assert!(
                pool.get(key).is_some(),
                "target hunch `{}` declares atom_pool but not under its domain `{}` — pool keys: {:?}",
                t.hunch,
                key,
                pool.as_object().map(|o| o.keys().collect::<Vec<_>>()),
            );
        }
    }
}
