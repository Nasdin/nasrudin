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
You have FOUR load-bearing levers:\n\
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
     emit a pool.\n\
  4. `proposed_chains` — full derivation chains, keyed by target name. \
     Each chain is an ordered list of RuleStep objects. When a worker \
     is running the target you've named, it injects your chain as an \
     elite individual at chunk start so the GA explores neighbourhoods \
     of your candidate. Use this when you can enumerate the upstream \
     derivation directly: a pure-random GA over 195k axioms cannot \
     compose an 8-step chain like `rest_energy_from_upstream`, but you \
     can write it out in one shot. Do NOT reference forbidden \
     headline axioms (e.g. `mass_shell_condition`, `emc_squared`) — \
     the no-cheat audit gates these at boot and the chain will be \
     rejected. Compose from upstream POSTULATES only: \
     `four_momentum_time_component`, `minkowski_invariant_def`, \
     `invariant_mass_postulate`, `rest_frame_psq_zero`, \
     `photon_energy_def`, `hbar_positive`, etc. Each step's `kind` \
     must be one of: `IntroduceAxiom`, `IntroduceTheorem`, \
     `SubstituteValue`, `AlgebraicSimplify`, `RearrangeEquation`, \
     `TakePositiveRoot`.\n\
  5. `proposed_targets` — up to 4 new exploration HEADLINES per cycle, \
     each `{ hunch: <LaTeX>, domain_hint: <snake_case domain>, \
     rationale: <1-2 sentences> }`. Use this when the existing platform \
     queue (E=mc², F=ma, S=k_B ln Ω, Schrödinger, EFE, Gauss) is mostly \
     in `proved` state — otherwise workers fall back to pure-random GA \
     between cycles. Their current lifecycle states are surfaced in the \
     prompt under `platform_target_states`. Each accepted entry is \
     enqueued as a new platform conjecture row at priority=2 (curated \
     headlines stay at 3 and still win ties). Do NOT propose hunches \
     that match the no-cheat audit deny-list (rest energy variants, \
     mass-shell, photon dispersion, Hubble's law, …) — they are dropped \
     with a warn. This is a curriculum-extension lever, not a \
     soft-target substitute.\n\n\
  6. `extension.strategy_genome_v1` — a compact AlphaEvolve-style \
     strategy genome. Use this to make large moves with few tokens: \
     one domain policy can scale compute, bias mutation operators, \
     shift suffix pressure, and adjust elitism. Workers treat it as a \
     candidate strategy; local RL/QD statistics decide whether it keeps \
     helping across chunks. Emit only the domains you want to change.\n\n\
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
  "proposed_chains": {
    "<target_id>": [
      { "kind": "IntroduceAxiom", "axiom_name": "four_momentum_time_component" },
      { "kind": "IntroduceAxiom", "axiom_name": "minkowski_invariant_def" },
      { "kind": "IntroduceAxiom", "axiom_name": "invariant_mass_postulate" },
      { "kind": "IntroduceAxiom", "axiom_name": "rest_frame_psq_zero" },
      { "kind": "AlgebraicSimplify" }
    ], ...
  }                          -- full LLM-proposed derivation chains keyed by
                                target_id (e.g. sr_rest_energy). Workers
                                injecting this as an elite seed at chunk
                                start when NASRUDIN_USE_LLM_CHAINS=1. The
                                example above is the (truncated) skeleton of
                                rest_energy_from_upstream — adapt for the
                                target you're proposing. Variants: `kind` ∈
                                {IntroduceAxiom (uses axiom_name),
                                 IntroduceTheorem (uses theorem_name for
                                 peer-verified results),
                                 SubstituteValue (var, value, reason),
                                 AlgebraicSimplify,
                                 RearrangeEquation (description, target),
                                 TakePositiveRoot}. Forbidden axioms (no-cheat
                                gate): mass_shell_condition, emc_squared,
                                anything that pre-encodes the headline.
                                Empty/missing → worker falls back to its
                                hardcoded m1_seed_elite_for registry,
  "proposed_targets": [
    { "hunch": "<LaTeX>",
      "domain_hint": "<snake_case domain>",
      "rationale": "<1-2 sentences>" }, ...
  ]                           -- up to 4 new exploration headlines per cycle.
                                Each accepted entry becomes a new
                                conjecture_jobs row with tier='platform',
                                provider='steerer-proposed', priority=2.
                                Use this when platform_target_states shows
                                most of the curated 6 headlines as `proved`
                                so workers don't fall back to pure-random
                                GA. Entries with non-parseable LaTeX,
                                unknown domain_hint, or canonical-form
                                matching the no-cheat audit deny-list are
                                dropped with a warn (the rest of the cycle
                                still applies). Don't propose hunches
                                already in the platform queue — the seeder
                                de-dupes by hunch but you waste a slot,
  "cluster_directives": [
    { "island_domain": "...",
      "centroid_skeleton_hash": <u64>,    -- copy from cluster_summaries above,
      "action": "boost"|"exploit"|"diversify"|"kill",
      "strength": <0..1> }
  ] -- empty in B,
  "extension": {
    "strategy_genome_v1": {
      "domain_policies": {
        "<domain>": {
          "compute_scale": <0.25..4.0>,
          "mutation_rate_mult": <0.25..4.0>,
          "suffix_bias_delta": <-1.0..1.0>,
          "elitism_delta": <-0.2..0.2>,
          "operator_bias": { "<op_name>": <0..4> }
        }
      }
    },
    "...": "other free-form fields"
  }                           -- compact high-level strategy genome.
                                Workers apply only the matching domain
                                policy in scope C, clamp all values, and
                                let local RL/QD statistics evaluate the
                                effect across chunks. This is the preferred
                                way to make large moves under the 10k-token
                                / 2h budget: emit a small policy instead of
                                verbose per-cluster micromanagement. Free-
                                form fields are persisted in history; unknown
                                fields are ignored by older workers,
  "lessons_learned": "<= 4000 chars; rolling notes. REPLACE each cycle
                      (don't append). Indefinite-horizon memory of what
                      worked / what didn't / current focus. Survives
                      past the 10-cycle history window.",
  "rationale": "<= 500 chars"
}"#;

const COMPACT_MAX_DEPTH: usize = 3;
const COMPACT_MAX_OBJECT_KEYS: usize = 32;
const COMPACT_MAX_ARRAY_ITEMS: usize = 8;
const COMPACT_MAX_STRING_CHARS: usize = 180;
const COMPACT_MAX_SUMMARY_BYTES: usize = 600;

fn compact_cluster_summary_for_llm(value: &serde_json::Value) -> serde_json::Value {
    let compacted = compact_value_for_llm(value, 0);
    let bytes = serde_json::to_vec(&compacted).map(|v| v.len()).unwrap_or(0);
    if bytes <= COMPACT_MAX_SUMMARY_BYTES {
        return compacted;
    }
    match compacted {
        serde_json::Value::Object(map) => {
            let mut out = serde_json::Map::new();
            for key in [
                "domain",
                "island_domain",
                "cluster_id",
                "centroid_skeleton_hash",
                "mean_fitness",
                "max_fitness",
                "verified_count",
                "lake_attempts",
                "lake_passed",
                "rl_policy_evidence",
                "target_progress",
                "novelty",
                "generation",
            ] {
                if let Some(v) = map.get(key) {
                    out.insert(key.to_string(), v.clone());
                }
            }
            out.insert(
                "compacted".into(),
                serde_json::Value::String(format!(
                    "summary exceeded {COMPACT_MAX_SUMMARY_BYTES} bytes; retained core scalar evidence"
                )),
            );
            serde_json::Value::Object(out)
        }
        other => other,
    }
}

fn compact_value_for_llm(value: &serde_json::Value, depth: usize) -> serde_json::Value {
    if depth >= COMPACT_MAX_DEPTH {
        return match value {
            serde_json::Value::Object(map) => serde_json::json!({
                "object_keys": map.keys().take(12).cloned().collect::<Vec<_>>(),
                "dropped": "max_depth"
            }),
            serde_json::Value::Array(items) => serde_json::json!({
                "array_len": items.len(),
                "dropped": "max_depth"
            }),
            other => compact_scalar_for_llm(other),
        };
    }
    match value {
        serde_json::Value::Object(map) => {
            let mut out = serde_json::Map::new();
            for (key, child) in map {
                if out.len() >= COMPACT_MAX_OBJECT_KEYS {
                    out.insert(
                        "_truncated_keys".into(),
                        serde_json::Value::String("object key cap reached".into()),
                    );
                    break;
                }
                if keep_cluster_evidence_key(key) {
                    out.insert(key.clone(), compact_value_for_llm(child, depth + 1));
                }
            }
            serde_json::Value::Object(out)
        }
        serde_json::Value::Array(items) => serde_json::Value::Array(
            items
                .iter()
                .take(COMPACT_MAX_ARRAY_ITEMS)
                .map(|v| compact_value_for_llm(v, depth + 1))
                .collect(),
        ),
        other => compact_scalar_for_llm(other),
    }
}

fn compact_scalar_for_llm(value: &serde_json::Value) -> serde_json::Value {
    match value {
        serde_json::Value::String(s) if s.chars().count() > COMPACT_MAX_STRING_CHARS => {
            let truncated: String = s.chars().take(COMPACT_MAX_STRING_CHARS).collect();
            serde_json::Value::String(format!("{truncated}…[truncated]"))
        }
        other => other.clone(),
    }
}

fn keep_cluster_evidence_key(key: &str) -> bool {
    let k = key.to_ascii_lowercase();
    if [
        "lean_source",
        "source",
        "stderr",
        "stdout",
        "raw",
        "population",
        "individuals",
        "chains",
        "examples",
        "samples",
        "logs",
    ]
    .iter()
    .any(|needle| k.contains(needle))
    {
        return false;
    }
    [
        "domain",
        "island",
        "cluster",
        "centroid",
        "skeleton",
        "hash",
        "fitness",
        "reward",
        "verified",
        "lake",
        "pass",
        "attempt",
        "target",
        "novel",
        "novelty",
        "mean",
        "max",
        "min",
        "count",
        "candidate",
        "unique",
        "generation",
        "operator",
        "policy",
        "mutation",
        "qd",
        "archive",
        "cell",
        "progress",
        "elapsed",
        "duration",
        "strategy",
        "genome",
    ]
    .iter()
    .any(|needle| k.contains(needle))
}

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
    platform_target_states: &[serde_json::Value],
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
    let cluster_summaries_compact: Vec<serde_json::Value> = cluster_summaries
        .iter()
        .map(compact_cluster_summary_for_llm)
        .collect();
    let payload = serde_json::json!({
        "schema": SCHEMA_HINT,
        "scope": scope,
        "history_newest_first": history,
        "previous_lessons_learned": previous_lessons_learned,
        "current_demand": demand,
        "active_paid_jobs": active_jobs,
        "cluster_summaries": cluster_summaries_compact,
        "cluster_summary_compaction": {
            "policy": "lossy evidence condenser",
            "kept": "domain/cluster ids, fitness/reward, verifier, target progress, novelty, QD, mutation/operator stats, compact RL policy evidence",
            "dropped": "raw populations, example chains, Lean source, stdout/stderr/log blobs",
            "max_summary_bytes": COMPACT_MAX_SUMMARY_BYTES
        },
        "bandit_state": bandit_state,
        "k_per_island_next": k_per_island_next,
        "in_flight_targets": in_flight_targets,
        "platform_target_states": platform_target_states,
        "instructions": format!("scope={scope}. {mode_note} \
            Cluster directives address clusters by `centroid_skeleton_hash` \
            from the cluster_summaries above. The bandit (not you) chose \
            k_per_island_next; cross-reference bandit_state to understand \
            why. \
            \n\nRL/GA division of labor: cluster_summaries may contain \
            `rl_policy_evidence` from the local worker episode evaluator. \
            Treat it as condensed evidence about which GA workhorse and \
            target-selector policies are paying off. Do not request raw logs, \
            populations, Lean source, or per-step micromanagement. Use this \
            evidence only for sparse high-level moves: domain weights, \
            mutation priors, atom pools, soft targets, and compact strategy \
            genomes. The worker RL layer owns per-chunk policy choice. \
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
            \n\nPlatform curriculum extension: platform_target_states lists \
            the 6 curated headlines (E=mc², F=ma, S=k_B ln Ω, Schrödinger, \
            EFE, Gauss's law) with their current state — queued / claimed \
            / running / proved / budget_exhausted / cancelled. When most \
            entries are terminal (proved or otherwise done) the queue is \
            running dry; emit up to 4 `proposed_targets` to graft fresh \
            headlines on so workers stay on directed search instead of \
            falling back to random GA. Empty/null platform_target_states \
            means the platform queue hasn't been seeded yet — skip this \
            lever. \
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
        Vec<serde_json::Value>,
    ) {
        (
            vec![],
            serde_json::json!({}),
            std::collections::HashMap::new(),
            vec![],
            vec![],
        )
    }

    #[test]
    fn prompt_includes_scope_and_demand() {
        let (cs, bs, kp, ift, pts) = empty_extras();
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
            &pts,
        );
        assert!(p.contains("scope=C"));
        assert!(p.contains("entropy"));
    }

    #[test]
    fn mode_b_signals_pinned_targets() {
        let (cs, bs, kp, ift, pts) = empty_extras();
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
            &pts,
        );
        assert!(p.contains("scope=B"));
        assert!(p.contains("LOCKED"));
        assert!(p.contains("delta Q = T dS"));
    }

    #[test]
    fn schema_mentions_required_fields() {
        let (cs, bs, kp, ift, pts) = empty_extras();
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cs,
            &bs,
            &kp,
            &ift,
            "",
            &pts,
        );
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
    fn prompt_compacts_cluster_summaries_before_llm() {
        let (_, bs, kp, ift, pts) = empty_extras();
        let cluster_summaries = vec![serde_json::json!({
            "domain": "qm",
            "centroid_skeleton_hash": 12345,
            "mean_fitness": 0.42,
            "lake_attempts": 3,
            "lake_passed": 1,
            "target_progress": 0.75,
            "mutation_operator_stats": { "append_productive_suffix": { "pulls": 9, "reward": 1.2 } },
            "rl_policy_evidence": {
                "ga_policy": "lake_focus",
                "ga_policy_conservative_score": 0.81,
                "ga_policy_lake_pass_rate": 0.50,
                "target_selector_policy": "verifier_ucb"
            },
            "example_chains": [{ "kind": "IntroduceAxiom", "axiom_name": "huge" }],
            "lean_source": "theorem huge := by sorry",
            "stderr": "x".repeat(5000),
        })];
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cluster_summaries,
            &bs,
            &kp,
            &ift,
            "",
            &pts,
        );
        assert!(p.contains("centroid_skeleton_hash"));
        assert!(p.contains("lake_passed"));
        assert!(p.contains("target_progress"));
        assert!(p.contains("append_productive_suffix"));
        assert!(p.contains("rl_policy_evidence"));
        assert!(p.contains("lake_focus"));
        assert!(p.contains("ga_policy_conservative_score"));
        assert!(p.contains("RL/GA division of labor"));
        assert!(p.contains("The worker RL layer owns per-chunk policy choice"));
        assert!(!p.contains("example_chains"));
        assert!(!p.contains("theorem huge"));
        assert!(!p.contains("\"stderr\""));
        assert!(p.contains("cluster_summary_compaction"));
    }

    #[test]
    fn compact_cluster_summary_bounds_long_strings() {
        let summary = serde_json::json!({
            "domain": "sr",
            "reward_explanation": "r".repeat(1000),
            "lake_attempts": 1
        });
        let compact = compact_cluster_summary_for_llm(&summary);
        let encoded = serde_json::to_string(&compact).unwrap();
        assert!(encoded.contains("[truncated]"));
        assert!(encoded.len() < 500);
    }

    #[test]
    fn schema_hint_lists_mutation_priors_and_op_names() {
        let (cs, bs, kp, ift, pts) = empty_extras();
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cs,
            &bs,
            &kp,
            &ift,
            "",
            &pts,
        );
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
        let (cs, bs, kp, ift, pts) = empty_extras();
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
            &pts,
        );
        assert!(p.contains("previous_lessons_learned"));
        assert!(p.contains("Boost@SR strength=0.5"));
    }

    #[test]
    fn schema_hint_documents_lessons_learned() {
        let (cs, bs, kp, ift, pts) = empty_extras();
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cs,
            &bs,
            &kp,
            &ift,
            "",
            &pts,
        );
        assert!(
            p.contains("lessons_learned"),
            "schema must mention lessons_learned"
        );
    }

    #[test]
    fn system_prompt_documents_proposed_chains() {
        assert!(
            SYSTEM_PROMPT.contains("proposed_chains"),
            "system prompt must document the proposed_chains lever"
        );
        // The four allowed RuleStep variants must be enumerated so the
        // LLM knows what `kind` strings to emit.
        for variant in &[
            "IntroduceAxiom",
            "IntroduceTheorem",
            "AlgebraicSimplify",
            "RearrangeEquation",
        ] {
            assert!(
                SYSTEM_PROMPT.contains(variant),
                "system prompt must mention RuleStep variant {variant}"
            );
        }
        assert!(
            SYSTEM_PROMPT.contains("forbidden"),
            "system prompt must warn about forbidden headline axioms"
        );
    }

    #[test]
    fn schema_hint_documents_proposed_chains() {
        let (cs, bs, kp, ift, pts) = empty_extras();
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cs,
            &bs,
            &kp,
            &ift,
            "",
            &pts,
        );
        assert!(
            p.contains("proposed_chains"),
            "schema hint must document proposed_chains shape"
        );
        // The example chain in the schema hint should reference at
        // least one real upstream axiom so the LLM has a concrete
        // anchor to imitate.
        assert!(
            p.contains("four_momentum_time_component") || p.contains("IntroduceAxiom"),
            "schema hint should include a worked RuleStep example"
        );
    }

    #[test]
    fn system_prompt_documents_proposed_targets() {
        assert!(
            SYSTEM_PROMPT.contains("proposed_targets"),
            "system prompt must teach the proposed_targets lever"
        );
        assert!(
            SYSTEM_PROMPT.contains("proved"),
            "system prompt must mention when to propose (most platform headlines proved)"
        );
    }

    #[test]
    fn schema_hint_documents_proposed_targets() {
        let (cs, bs, kp, ift, pts) = empty_extras();
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cs,
            &bs,
            &kp,
            &ift,
            "",
            &pts,
        );
        for f in &["proposed_targets", "hunch", "domain_hint", "rationale"] {
            assert!(
                p.contains(f),
                "schema hint must mention proposed_targets field: {f}"
            );
        }
    }

    #[test]
    fn system_prompt_documents_strategy_genome() {
        assert!(
            SYSTEM_PROMPT.contains("strategy_genome_v1"),
            "system prompt must teach the compact strategy-genome lever"
        );
        assert!(
            SYSTEM_PROMPT.contains("AlphaEvolve"),
            "system prompt should connect strategy genomes to AlphaEvolve-style search"
        );
    }

    #[test]
    fn schema_hint_documents_strategy_genome() {
        let (cs, bs, kp, ift, pts) = empty_extras();
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cs,
            &bs,
            &kp,
            &ift,
            "",
            &pts,
        );
        for f in &[
            "strategy_genome_v1",
            "domain_policies",
            "compute_scale",
            "operator_bias",
        ] {
            assert!(
                p.contains(f),
                "schema hint must mention strategy genome field: {f}"
            );
        }
    }

    #[test]
    fn prompt_surfaces_platform_target_states() {
        let (cs, bs, kp, ift, _) = empty_extras();
        let pts = vec![serde_json::json!({
            "hunch": "E = m * c^2",
            "state": "proved",
        })];
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cs,
            &bs,
            &kp,
            &ift,
            "",
            &pts,
        );
        assert!(p.contains("platform_target_states"));
        assert!(p.contains("E = m * c^2"));
    }

    #[test]
    fn instructions_explain_rolling_memory() {
        let (cs, bs, kp, ift, pts) = empty_extras();
        let p = build_prompt(
            "C",
            &[],
            &DemandSnapshot::default(),
            &[],
            &cs,
            &bs,
            &kp,
            &ift,
            "",
            &pts,
        );
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
