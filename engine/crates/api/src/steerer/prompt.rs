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
you have full authority.\n\n\
The GA discovers theorems by chaining axioms and mutating the chain. \
You have three load-bearing levers:\n\
  1. `mutation_priors` — bias which mutation operators run more often. \
     Boost `append_productive_suffix` when chains are reaching novel \
     equations; boost `mutate_axiom_name` when chains are stagnating.\n\
  2. `soft_targets` — name a physics result you want the explorer fleet \
     to chase. Set `target_id` to the stable handle of a known target \
     (e.g. `sr_rest_energy`, `qm_schrodinger`, `em_gauss_law`, \
     `newton_second`, `gr_einstein_field_equation`) and workers wire \
     it into their fitness via ladder-progress scoring. Use this as \
     your curriculum: propose one target per domain, watch outcomes, \
     advance via `target_status_updates` when verified.\n\
  3. `atom_pool` — per-domain physics-shape compounds used by \
     `append_productive_suffix` to synthesise candidate target \
     equations. Without atoms the suffix can only cycle axioms; with \
     domain-appropriate compounds it can synthesise productive \
     `X² = Y²` targets. Recognised atom names: `m_c_sq`, `c_p0`, \
     `p0_sq`, `m_sq_c_sq`, `e_sq`, `p0_sq_minus_psq`, `m_c`, `c_sq` \
     (SR baseline); workers fall back to the baseline when you don't \
     emit a pool.\n\n\
Keep rationale ≤500 chars; rewrite `lessons_learned` each cycle as a \
rolling indefinite-horizon memory of what works.";

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
  "soft_targets": [
    { "latex": "E = m c^2",
      "domain": "special_relativity",
      "weight": <0..1>,
      "target_id": "sr_rest_energy"  -- stable handle; when set to a known
                                        spec name the worker wires it into
                                        ladder-progress fitness automatically.
                                        Known IDs: sr_rest_energy,
                                        qm_schrodinger, qm_planck_einstein,
                                        qm_de_broglie, qm_free_particle_dispersion,
                                        qm_harmonic_oscillator,
                                        thermo_boltzmann_entropy, thermo_carnot,
                                        newton_second, em_gauss_law,
                                        gr_einstein_field_equation,
                                        gr_schwarzschild_radius
    }, ...
  ],
  "hard_targets": [ ... ] -- empty in B,
  "mutation_knobs": { "rate": <0.05..0.30>, "suffix_bias": <0..1>,
                      "population_size": <32..512>, "elitism_fraction": <0..0.2> }
                     -- null in B,
  "mutation_priors": { "<op_name>": <0..2> }
                     -- op_name ∈ ["insert_random", "delete_random",
                                   "swap_adjacent", "mutate_axiom_name",
                                   "mutate_param", "append_productive_suffix"];
                        unknown keys ignored; missing → uniform 1.0,
  "atom_pool": {
    "<domain>": [ { "name": "m_c_sq", "weight": <0..4> }, ... ]
  }                          -- per-domain physics-shape compounds for
                                `append_productive_suffix` to draw from.
                                Recognised SR atoms (workers may ignore
                                unknowns, so adding new names is forward-safe):
                                m_c_sq, c_p0, p0_sq, m_sq_c_sq, e_sq,
                                p0_sq_minus_psq, m_c, c_sq. Empty/missing →
                                uniform fallback to hardcoded 8-atom baseline.
                                Use this to give EM/QM/GR domains their own
                                physics-shape pool so the suffix mechanism
                                can synthesise non-SR productive targets,
  "cluster_directives": [
    { "island_domain": "...",
      "centroid_skeleton_hash": <u64>,    -- copy from cluster_summaries above,
      "action": "boost"|"exploit"|"diversify"|"kill",
      "strength": <0..1> }
  ] -- empty in B,
  "extension": <any JSON>     -- free-form pass-through. Use this to
                                  experiment with directive shapes the
                                  current daemon doesn't recognise yet
                                  (proof plans, axiom hints, etc.).
                                  Persisted in history; ignored by the
                                  GA until a future version reads it,
  "lessons_learned": "<= 4000 chars; rolling notes. REPLACE each cycle
                      (don't append). Indefinite-horizon memory of what
                      worked / what didn't / current focus. Survives
                      past the 10-cycle history window.",
  "rationale": "<= 500 chars"
}"#;

/// Build the *user* prompt string. Caller separately supplies the
/// system prompt to the LLM SDK. We bundle everything as one JSON
/// object so the model parses it into a single coherent context.
///
/// `cluster_summaries` are the most-recent ClusterSummary JSONs the
/// API received from workers; the LLM uses them to reason about per-
/// cluster directives (addressed by `centroid_skeleton_hash`).
/// `bandit_state` is `domain → [{k, pulls, mean_reward}]` so the LLM
/// can cross-reference its directive history with which K worked.
/// `k_per_island_next` is the bandit's just-chosen K per island —
/// the LLM does NOT pick K, but seeing it helps it interpret the
/// next chunk's cluster_summaries.
pub fn build_prompt(
    scope: &str,
    history: &[HistoryEntry],
    demand: &DemandSnapshot,
    active_jobs: &[ActiveJobSummary],
    cluster_summaries: &[serde_json::Value],
    bandit_state: &serde_json::Value,
    k_per_island_next: &std::collections::HashMap<String, u32>,
    in_flight_targets: &[serde_json::Value],
    previous_lessons_learned: &str,
) -> String {
    let mode_note = if scope == "B" {
        "Mutation knobs are LOCKED for this cycle (≥1 paid Researcher \
        job is running). Set mutation_knobs=null, hard_targets=[], \
        cluster_directives=[]. Use soft_targets to bias the explorer \
        fleet toward prerequisite lemmas in the active-job domains."
    } else {
        "Full authority. You may emit hard_targets, mutation_knobs, \
        mutation_priors, and cluster_directives."
    };
    let payload = serde_json::json!({
        "schema": SCHEMA_HINT,
        "scope": scope,
        "history_newest_first": history,
        "previous_lessons_learned": previous_lessons_learned,
        "current_demand": demand,
        "active_paid_jobs": active_jobs,
        "cluster_summaries": cluster_summaries,
        "bandit_state": bandit_state,
        "k_per_island_next": k_per_island_next,
        "in_flight_targets": in_flight_targets,
        "instructions": format!("scope={scope}. {mode_note} \
            Cluster directives address clusters by `centroid_skeleton_hash` \
            from the cluster_summaries above. The bandit (not you) chose \
            k_per_island_next; cross-reference bandit_state to understand \
            why. \
            \n\nSelf-curriculum: in_flight_targets lists targets you've \
            proposed in past cycles that are still open or proving. Inspect \
            recent verified theorems in the cycle outcomes; if any matches \
            an in-flight target, emit a target_status_updates entry to mark \
            it proved (or abandoned, if the GA has demonstrably given up). \
            Propose new soft_targets with stable target_id strings (suggest \
            UUIDs or descriptive slugs) so future cycles can track them. \
            \n\nIndefinite-horizon memory: previous_lessons_learned is the \
            rolling notes you maintained across past cycles. It survives \
            past the 10-cycle history_newest_first window — anything you \
            want to remember beyond that buffer must live here. Each cycle, \
            REPLACE the previous version with an updated one (rolling, not \
            appending): keep insights still relevant, drop stale ones, fold \
            in new observations from this cycle's outcome. Cap ≤4000 chars. \
            Cover what experiments worked, what didn't (so you don't repeat \
            mistakes), and your current focus. Emit it as the \
            `lessons_learned` field. \
            \nEmit SteeringConfig JSON only — no prose, no markdown fences."),
    });
    serde_json::to_string_pretty(&payload).unwrap_or_else(|_| "{}".into())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn empty_extras() -> (
        Vec<serde_json::Value>,
        serde_json::Value,
        std::collections::HashMap<String, u32>,
        Vec<serde_json::Value>,
    ) {
        (
            vec![],
            serde_json::json!({}),
            std::collections::HashMap::new(),
            vec![],
        )
    }

    #[test]
    fn prompt_includes_scope_and_demand() {
        let (cs, bs, kp, ift) = empty_extras();
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
            &cs,
            &bs,
            &kp,
            &ift,
            "",
        );
        assert!(p.contains("scope=C"));
        assert!(p.contains("entropy"));
    }

    #[test]
    fn mode_b_signals_pinned_targets() {
        let (cs, bs, kp, ift) = empty_extras();
        let p = build_prompt(
            "B",
            &[],
            &DemandSnapshot::default(),
            &[ActiveJobSummary {
                domain: "thermodynamics".into(),
                conjecture_summary: "delta Q = T dS".into(),
            }],
            &cs,
            &bs,
            &kp,
            &ift,
            "",
        );
        assert!(p.contains("scope=B"));
        assert!(p.contains("LOCKED"));
        assert!(p.contains("delta Q = T dS"));
    }

    #[test]
    fn schema_mentions_required_fields() {
        let (cs, bs, kp, ift) = empty_extras();
        let p =
            build_prompt("C", &[], &DemandSnapshot::default(), &[], &cs, &bs, &kp, &ift, "");
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
        let (cs, bs, kp, ift) = empty_extras();
        let p =
            build_prompt("C", &[], &DemandSnapshot::default(), &[], &cs, &bs, &kp, &ift, "");
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

    #[test]
    fn prompt_surfaces_previous_lessons_learned() {
        let (cs, bs, kp, ift) = empty_extras();
        let lessons = "Boost@SR strength=0.5 → 1.5× has worked across 4 of last 6 cycles.";
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cs,
            &bs,
            &kp,
            &ift,
            lessons,
        );
        assert!(p.contains("previous_lessons_learned"));
        assert!(p.contains("Boost@SR strength=0.5"));
    }

    #[test]
    fn schema_hint_documents_lessons_learned() {
        let (cs, bs, kp, ift) = empty_extras();
        let p =
            build_prompt("C", &[], &DemandSnapshot::default(), &[], &cs, &bs, &kp, &ift, "");
        assert!(
            p.contains("lessons_learned"),
            "schema must mention lessons_learned"
        );
    }

    #[test]
    fn instructions_explain_rolling_memory() {
        let (cs, bs, kp, ift) = empty_extras();
        let p =
            build_prompt("C", &[], &DemandSnapshot::default(), &[], &cs, &bs, &kp, &ift, "");
        assert!(
            p.contains("REPLACE the previous version"),
            "instructions must tell the LLM to replace not append"
        );
        assert!(
            p.contains("Indefinite-horizon memory")
                || p.contains("indefinite-horizon")
                || p.contains("survives"),
            "instructions must explain why lessons_learned matters"
        );
    }
}
