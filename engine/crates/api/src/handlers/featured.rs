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
                // Found a real theorem in the corpus
                let cycle = if let Some(generation_num) = theorem.generation {
                    format!("GA-cycle {}", generation_num)
                } else {
                    "GA-cycle unknown".to_string()
                };

                let elapsed = if let Some(duration_ms) = theorem.verification_duration_ms {
                    let seconds = duration_ms / 1000;
                    let days = seconds / 86400;
                    let hours = (seconds % 86400) / 3600;
                    if days > 0 {
                        format!("{} d · {} h", days, hours)
                    } else if hours > 0 {
                        format!("{} h", hours)
                    } else {
                        format!("{} s", seconds)
                    }
                } else {
                    "unknown".to_string()
                };

                // Estimate proof lines from lean source (count lines)
                let proof_lines = Some(theorem.lean_source.lines().count() as i32);

                let note = format!(
                    "Verified theorem from the corpus with {} axioms used.",
                    theorem.axioms_used.len()
                );

                FeaturedDiscovery {
                    formula: target.latex.to_string(),
                    name: target.name.to_string(),
                    domain: target.domain.to_string(),
                    found: true,
                    cycle,
                    elapsed,
                    proof_lines,
                    note,
                }
            }
            None => {
                // Not found in corpus yet - show searching state
                let note = format!(
                    "Searching corpus for {} theorems matching this formula.",
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
                    note,
                }
            }
        };

        discoveries.push(discovery);
    }

    (StatusCode::OK, Json(discoveries)).into_response()
}

/// Try to find a theorem matching the target formula in the corpus.
///
/// This is a simple heuristic search - it looks for verified theorems in the
/// target domain that contain the canonical patterns.
async fn find_matching_theorem(
    db: &sea_orm::DatabaseConnection,
    target: &TargetFormula,
) -> Option<nasrudin_pg::entity::theorems::Model> {
    use sea_orm::{ColumnTrait, EntityTrait, QueryFilter, QueryOrder, QuerySelect};

    // Recent verified theorems in the target domain. We pull whole rows
    // (not a tuple projection) because `theorems.id` is bytea, not text,
    // and we need the latex column anyway for pattern matching.
    let candidates = nasrudin_pg::entity::theorems::Entity::find()
        .filter(nasrudin_pg::entity::theorems::Column::Status.eq("Verified"))
        .filter(nasrudin_pg::entity::theorems::Column::Domain.eq(target.domain))
        .order_by_desc(nasrudin_pg::entity::theorems::Column::VerifiedAt)
        .limit(100)
        .all(db)
        .await
        .ok()?;

    let mut best: Option<(nasrudin_pg::entity::theorems::Model, usize)> = None;
    for thm in candidates {
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
