//! Build the LLM prompt for one steerer cycle.
//!
//! The system prompt is constant — it tells the model what it is, what
//! the schema looks like, and how scopes B and C differ. The user
//! prompt is one JSON object containing the full context: history of
//! recent cycles, current demand snapshot, currently-running paid
//! jobs, and per-cycle instructions. The model is asked to reply with
//! ONLY a JSON document matching `SteeringConfig`.

use serde::{Deserialize, Serialize};

use crate::steerer::demand::DemandSnapshot;

/// Constant system prompt shipped on every cycle. Kept short so we
/// don't burn tokens; the schema details live in the user-prompt
/// payload where they can change without touching code.
pub const SYSTEM_PROMPT: &str = "You are the cluster steerer for Nasrudin, a distributed \
theorem-discovery platform. Each cycle, read aggregate user demand and \
the outcomes of your last 10 cycles, then emit a SteeringConfig JSON \
that biases the GA exploration of thousands of workers. Output ONLY \
valid JSON matching the schema. Honor the scope: in scope B (paid \
jobs running) set hard_targets=[] and mutation_knobs=null; in scope C \
you have full authority. When you observe a cluster making productive \
use of `append_productive_suffix` or `mutate_axiom_name`, bias \
`mutation_priors` toward those operators (default uniform 1.0). \
Keep rationale ≤500 chars.";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActiveJobSummary {
    pub domain: String,
    pub conjecture_summary: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistoryEntry {
    pub config: serde_json::Value,
    pub outcome: Option<serde_json::Value>,
    pub scope: String,
    pub started_at: String,
    pub validation_failed: bool,
}

/// The schema-of-output we paste into the prompt so the model knows
/// what to emit. Kept in sync with `schema::SteeringConfig` manually
/// because rust-side reflection doesn't get us a JSON Schema for free
/// without an extra dep.
const SCHEMA_HINT: &str = r#"{
  "version": 1,
  "scope": "B" | "C",
  "domain_weights": { "<domain>": <0..1>, ... } -- must sum to 1.0,
  "axiom_emphasis": { "<axiom_id>": <0..2> },
  "fitness_weights": {
    "novelty": <0..1>, "dimensional_elegance": <0..1>,
    "chain_length_penalty": <0..1>, "target_proximity": <0..1>
  } -- must sum to 1.0,
  "soft_targets": [ { "latex": "...", "domain": "...", "weight": <0..1> } ],
  "hard_targets": [ ... ] -- empty in B,
  "mutation_knobs": { "rate": <0.05..0.30>, "suffix_bias": <0..1>,
                      "population_size": <32..512>, "elitism_fraction": <0..0.2> }
                     -- null in B,
  "mutation_priors": { "<op_name>": <0..2> }
                     -- op_name ∈ ["insert_random", "delete_random",
                                   "swap_adjacent", "mutate_axiom_name",
                                   "mutate_param", "append_productive_suffix"];
                        unknown keys ignored; missing → uniform 1.0,
  "rationale": "<= 500 chars"
}"#;

/// Build the *user* prompt string. Caller separately supplies the
/// system prompt to the LLM SDK. We bundle everything as one JSON
/// object so the model parses it into a single coherent context.
pub fn build_prompt(
    scope: &str,
    history: &[HistoryEntry],
    demand: &DemandSnapshot,
    active_jobs: &[ActiveJobSummary],
) -> String {
    let mode_note = if scope == "B" {
        "Mutation knobs are LOCKED for this cycle (≥1 paid Researcher \
        job is running). Set mutation_knobs=null and hard_targets=[]. \
        Use soft_targets to bias the explorer fleet toward prerequisite \
        lemmas in the active-job domains."
    } else {
        "Full authority. You may emit hard_targets and mutation_knobs."
    };
    let payload = serde_json::json!({
        "schema": SCHEMA_HINT,
        "scope": scope,
        "history_newest_first": history,
        "current_demand": demand,
        "active_paid_jobs": active_jobs,
        "instructions": format!("scope={scope}. {mode_note} Emit SteeringConfig JSON only — no prose, no markdown fences."),
    });
    serde_json::to_string_pretty(&payload).unwrap_or_else(|_| "{}".into())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prompt_includes_scope_and_demand() {
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot {
                window_seconds: 600,
                top_saved_searches: vec![("entropy".into(), 4)],
                targeted_search_count: 1,
                active_hunches: vec![],
            },
            &[],
        );
        assert!(p.contains("scope=C"));
        assert!(p.contains("entropy"));
    }

    #[test]
    fn mode_b_signals_pinned_targets() {
        let p = build_prompt(
            "B",
            &[],
            &DemandSnapshot::default(),
            &[ActiveJobSummary {
                domain: "thermodynamics".into(),
                conjecture_summary: "delta Q = T dS".into(),
            }],
        );
        assert!(p.contains("scope=B"));
        assert!(p.contains("LOCKED"));
        assert!(p.contains("delta Q = T dS"));
    }

    #[test]
    fn schema_mentions_required_fields() {
        let p = build_prompt("C", &[], &DemandSnapshot::default(), &[]);
        for f in &[
            "version",
            "scope",
            "domain_weights",
            "fitness_weights",
            "mutation_knobs",
        ] {
            assert!(p.contains(f), "prompt missing schema field: {f}");
        }
    }

    #[test]
    fn schema_hint_lists_mutation_priors_and_op_names() {
        let p = build_prompt("C", &[], &DemandSnapshot::default(), &[]);
        assert!(
            p.contains("mutation_priors"),
            "schema must mention mutation_priors"
        );
        for op in &[
            "insert_random",
            "delete_random",
            "swap_adjacent",
            "mutate_axiom_name",
            "mutate_param",
            "append_productive_suffix",
        ] {
            assert!(p.contains(op), "schema must list operator name {op}");
        }
    }
}
