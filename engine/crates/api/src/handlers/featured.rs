//! `GET /api/featured` — fetch featured physics rediscoveries from the corpus.
//!
//! This endpoint returns a list of target physics formulas we're searching for,
//! along with their actual discovery status from the corpus. If a formula has been
//! discovered, it returns real theorem data; otherwise, it returns a "searching" state.

use axum::{
    Json,
    extract::State,
    http::StatusCode,
    response::IntoResponse,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::state::AppState;

/// Target physics formulas we're searching for in the corpus.
const TARGET_FORMULAS: &[TargetFormula] = &[
    TargetFormula {
        name: "Mass-energy equivalence",
        latex: "E = mc^2",
        domain: "Special relativity",
        // Try to match by canonical statement patterns
        canonical_patterns: &["energy", "mass", "c^2", "speed_of_light"],
    },
    TargetFormula {
        name: "Newton's second law",
        latex: "F = ma",
        domain: "Classical mechanics",
        canonical_patterns: &["force", "mass", "acceleration"],
    },
    TargetFormula {
        name: "Boltzmann entropy",
        latex: "S = k_B \\ln \\Omega",
        domain: "Statistical mechanics",
        canonical_patterns: &["entropy", "boltzmann", "ln"],
    },
    TargetFormula {
        name: "Schrödinger equation",
        latex: "i\\hbar\\dot\\psi = \\hat H \\psi",
        domain: "Quantum mechanics",
        canonical_patterns: &["schrodinger", "psi", "hamiltonian"],
    },
    TargetFormula {
        name: "Einstein field equations",
        latex: "R_{\\mu\\nu} - \\tfrac12 g_{\\mu\\nu} R = 8\\pi T_{\\mu\\nu}",
        domain: "General relativity",
        canonical_patterns: &["einstein", "field", "ricci", "tensor"],
    },
    TargetFormula {
        name: "Gauss's law",
        latex: "\\nabla\\cdot E = \\rho/\\varepsilon_0",
        domain: "Electromagnetism",
        canonical_patterns: &["gauss", "electric", "divergence", "charge"],
    },
];

struct TargetFormula {
    name: &'static str,
    latex: &'static str,
    domain: &'static str,
    canonical_patterns: &'static [&'static str],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeaturedDiscovery {
    pub formula: String,
    pub name: String,
    pub domain: String,
    pub found: bool,
    pub cycle: String,
    pub elapsed: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_lines: Option<i32>,
    /// Hex-encoded theorem id when `found = true`. Drives the
    /// landing-page card link to `/theorem/{id}`. `None` when the
    /// formula is still a search target.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub theorem_id: Option<String>,
    /// Count of parent theorems / axioms this derivation composed.
    /// Only set when `found = true`; zero indicates the matched row
    /// is an isolated lemma (which we now filter out at SQL time, so
    /// found rows should always have ≥ 1 here).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub axioms_used: Option<usize>,
    pub note: String,
}

/// `GET /api/featured` — return featured physics rediscoveries with real corpus status.
pub async fn featured(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({ "error": "pg_unavailable" })),
            )
                .into_response();
        }
    };

    let mut discoveries = Vec::new();

    for target in TARGET_FORMULAS {
        // Try to find a matching theorem in the corpus
        let match_result = find_matching_theorem(pg, target).await;

        let discovery = match match_result {
            Some(theorem) => {
                // Found a real GA-derived theorem. `find_matching_theorem`
                // guarantees generation ≥ 1 and a non-imported tactic, so
                // the cycle number reflects an actual GA generation rather
                // than the "0" that imported PhysLean axioms carry.
                let gen_num = theorem.generation.unwrap_or(0);
                let cycle = format!("Gen {}", gen_num);

                let elapsed = if let Some(duration_ms) = theorem.verification_duration_ms {
                    let seconds = duration_ms / 1000;
                    let days = seconds / 86400;
                    let hours = (seconds % 86400) / 3600;
                    if days > 0 {
                        format!("{} d · {} h", days, hours)
                    } else if hours > 0 {
                        format!("{} h", hours)
                    } else if seconds > 0 {
                        format!("{} s", seconds)
                    } else {
                        format!("{} ms", duration_ms)
                    }
                } else {
                    "—".to_string()
                };

                let proof_lines = Some(theorem.lean_source.lines().count() as i32);
                let axioms_count = theorem.axioms_used.len();
                let id_hex = hex::encode(&theorem.id);

                let note = format!(
                    "GA-derived chain at generation {} composed from {} axiom{}.",
                    gen_num,
                    axioms_count,
                    if axioms_count == 1 { "" } else { "s" }
                );

                FeaturedDiscovery {
                    formula: target.latex.to_string(),
                    name: target.name.to_string(),
                    domain: target.domain.to_string(),
                    found: true,
                    cycle,
                    elapsed,
                    proof_lines,
                    theorem_id: Some(id_hex),
                    axioms_used: Some(axioms_count),
                    note,
                }
            }
            None => {
                // Not yet GA-derived — show honest searching state.
                // (Imported PhysLean lemmas for this formula are
                // excluded by `find_matching_theorem`'s filters so we
                // never claim a static import as a "rediscovery".)
                let note = format!(
                    "No GA-derived chain matching this formula yet. Workers are searching the {} corpus.",
                    target.domain.to_lowercase()
                );

                FeaturedDiscovery {
                    formula: target.latex.to_string(),
                    name: target.name.to_string(),
                    domain: target.domain.to_string(),
                    found: false,
                    cycle: "search active".to_string(),
                    elapsed: "not yet discovered".to_string(),
                    proof_lines: None,
                    theorem_id: None,
                    axioms_used: None,
                    note,
                }
            }
        };

        discoveries.push(discovery);
    }

    (StatusCode::OK, Json(discoveries)).into_response()
}

/// Try to find a **GA-derived** theorem matching the target formula.
///
/// Excludes imported PhysLean/Mathlib axioms — these carry `generation = 0`,
/// `verification_tactic = 'imported'`, and `contributor_id = 'physlean'`,
/// and surfacing one as a "rediscovery" would be dishonest: imports are
/// the *input* to the search, not its output. A featured card only flips
/// to `found = true` when a worker has actually evolved a chain whose
/// final statement matches.
async fn find_matching_theorem(
    db: &sea_orm::DatabaseConnection,
    target: &TargetFormula,
) -> Option<nasrudin_pg::entity::theorems::Model> {
    use sea_orm::{ColumnTrait, Condition, EntityTrait, QueryFilter, QueryOrder, QuerySelect};

    let candidates = nasrudin_pg::entity::theorems::Entity::find()
        .filter(nasrudin_pg::entity::theorems::Column::Status.eq("Verified"))
        .filter(nasrudin_pg::entity::theorems::Column::Domain.eq(target.domain))
        // Exclude imported axioms: they are the seeds the GA composes
        // from, not derivations themselves. `verification_tactic` is
        // NULL for in-process GA discoveries and 'imported' for
        // PhysLean/Mathlib imports, so we accept the NULL case too.
        .filter(
            Condition::any()
                .add(nasrudin_pg::entity::theorems::Column::VerificationTactic.is_null())
                .add(nasrudin_pg::entity::theorems::Column::VerificationTactic.ne("imported")),
        )
        .filter(nasrudin_pg::entity::theorems::Column::ContributorId.ne("physlean"))
        // A real GA chain lives at generation ≥ 1; gen 0 means seed/axiom.
        .filter(nasrudin_pg::entity::theorems::Column::Generation.gt(0i64))
        .order_by_desc(nasrudin_pg::entity::theorems::Column::VerifiedAt)
        .limit(200)
        .all(db)
        .await
        .ok()?;

    let mut best: Option<(nasrudin_pg::entity::theorems::Model, usize)> = None;
    for thm in candidates {
        // Belt-and-braces: an axiom with no parents/axioms_used is also
        // not a real derivation, regardless of how it slipped past the
        // SQL filters above.
        if thm.axioms_used.is_empty() {
            continue;
        }
        let combined = format!(
            "{} {}",
            thm.canonical_statement.to_lowercase(),
            thm.latex.as_deref().unwrap_or("").to_lowercase(),
        );
        let score = target
            .canonical_patterns
            .iter()
            .filter(|p| combined.contains(*p))
            .count();
        if score > 0 && best.as_ref().is_none_or(|(_, s)| score > *s) {
            best = Some((thm, score));
        }
    }
    best.map(|(t, _)| t)
}
