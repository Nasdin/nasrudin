use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateConjectureRequest {
    pub hunch: String,
    #[serde(default)]
    pub domain_hint: Option<String>,
    pub provider: String,
    pub model: String,
    pub budget: BudgetSpec,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BudgetSpec {
    pub wall_seconds: u32,
    pub max_candidates: u32,
}

/// LLM-proposed search seed. The LLM's job-shaped contract — not a proof.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LlmSuggestion {
    pub axiom_set: Vec<String>,
    pub initial_population: Vec<String>,
    pub mutation_priors: HashMap<String, f32>,
    #[serde(default)]
    pub target_shape: Option<String>,
    pub rationale: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateConjectureResponse {
    pub job_id: Uuid,
    pub state: String,
    pub suggestions: Vec<LlmSuggestion>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StartConjectureRequest {
    pub chosen_index: i32,
    #[serde(default)]
    pub seed_overrides: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConjectureView {
    pub id: Uuid,
    pub state: String,
    pub outcome: Option<String>,
    pub hunch: String,
    pub domain_hint: Option<String>,
    pub provider: String,
    pub model: String,
    pub suggestions: Option<Vec<LlmSuggestion>>,
    pub chosen_index: Option<i32>,
    pub budget: BudgetSpec,
    pub candidates_attempted: i32,
    pub candidates_verified: i32,
    pub verified_theorem_ids: Vec<String>,
    pub created_at: DateTime<Utc>,
    pub completed_at: Option<DateTime<Utc>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConjectureListResponse {
    pub conjectures: Vec<ConjectureView>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_request_round_trips() {
        let req = CreateConjectureRequest {
            hunch: "energy and mass relate via c²".into(),
            domain_hint: Some("SpecialRelativity".into()),
            provider: "anthropic".into(),
            model: "claude-sonnet-4-6".into(),
            budget: BudgetSpec {
                wall_seconds: 600,
                max_candidates: 100_000,
            },
        };
        let json = serde_json::to_string(&req).unwrap();
        let back: CreateConjectureRequest = serde_json::from_str(&json).unwrap();
        assert_eq!(back.hunch, req.hunch);
        assert_eq!(back.budget.wall_seconds, 600);
        assert_eq!(back.budget.max_candidates, 100_000);
        assert_eq!(back.provider, "anthropic");
    }

    #[test]
    fn create_request_omits_domain_hint() {
        let json = r#"{"hunch":"x","provider":"anthropic","model":"m","budget":{"wall_seconds":10,"max_candidates":1}}"#;
        let req: CreateConjectureRequest = serde_json::from_str(json).unwrap();
        assert!(req.domain_hint.is_none());
    }

    #[test]
    fn suggestion_round_trips() {
        let s = LlmSuggestion {
            axiom_set: vec!["sr_invariant_interval".into()],
            initial_population: vec!["mass_shell".into(), "rest_energy".into()],
            mutation_priors: [("rearrange".into(), 0.7), ("substitute".into(), 0.3)]
                .into_iter()
                .collect(),
            target_shape: Some("E = m c^2".into()),
            rationale: "energy comes from inertial mass".into(),
        };
        let json = serde_json::to_string(&s).unwrap();
        let back: LlmSuggestion = serde_json::from_str(&json).unwrap();
        assert_eq!(back.axiom_set, s.axiom_set);
        assert_eq!(back.initial_population.len(), 2);
        assert_eq!(back.target_shape.as_deref(), Some("E = m c^2"));
    }

    #[test]
    fn start_request_omits_seed_overrides() {
        let json = r#"{"chosen_index":2}"#;
        let req: StartConjectureRequest = serde_json::from_str(json).unwrap();
        assert_eq!(req.chosen_index, 2);
        assert!(req.seed_overrides.is_none());
    }
}
