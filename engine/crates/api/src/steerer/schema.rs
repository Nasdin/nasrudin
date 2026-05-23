//! `SteeringConfig` — the contract between the cluster steerer and
//! every worker.
//!
//! Every cycle the LLM emits one of these. The validator rejects any
//! out-of-range value so a bad model response never poisons the
//! cluster (cycle.rs falls back to the last-known-good config). The
//! schema deliberately constrains all numeric ranges so a small model
//! that forgot a constraint emits something rejectable rather than
//! something that quietly causes drift.

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use thiserror::Error;

/// Top-level steering payload. Workers read `mutation_knobs` and the
/// fitness weights every chunk; targets and emphasis affect chain
/// composition and seed selection.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SteeringConfig {
    /// Schema version. Bumped when the wire format changes
    /// incompatibly so workers can refuse a future config they don't
    /// understand.
    pub version: u32,
    /// "B" or "C". See module docs.
    pub scope: String,
    /// Probability simplex over the supported physics domains. Must
    /// sum to 1.0 (±0.01).
    pub domain_weights: HashMap<String, f32>,
    /// Per-axiom multiplicative bias. Each value in [0.0, 2.0]; 1.0 is
    /// neutral, 0.0 effectively masks the axiom, 2.0 doubles its
    /// selection weight.
    pub axiom_emphasis: HashMap<String, f32>,
    /// Fitness shaping weights. Must sum to 1.0 (±0.01).
    pub fitness_weights: FitnessWeights,
    /// Aspirational targets — used as soft fitness bonuses. The
    /// explorer fleet is biased toward chains that approach these.
    pub soft_targets: Vec<SoftTarget>,
    /// Hard targets — the cluster will spawn dedicated explorer
    /// chains aimed at these expressions. Empty in scope=B.
    pub hard_targets: Vec<HardTarget>,
    /// GA tuning knobs. `None` in scope=B; `Some` in C.
    pub mutation_knobs: Option<MutationKnobs>,
    /// Per-operator mutation weight bias. Keys must be in MUTATION_OPS
    /// (defined in nasrudin_ga::chain_ga::MUTATION_OPS); unknown keys
    /// silently ignored on the GA side. Each value in [0.0, 2.0]; 1.0
    /// neutral. Empty/missing → uniform fallback.
    #[serde(default)]
    pub mutation_priors: HashMap<String, f32>,
    /// Per-cluster steering. Empty in scope=B (locked, like
    /// hard_targets/mutation_knobs). Each directive addresses a
    /// cluster by `centroid_skeleton_hash` from the previous chunk.
    #[serde(default)]
    pub cluster_directives: Vec<ClusterDirective>,
    /// Test-time compute-scaling directives. Empty in scope=B.
    /// Each directive's strength is bucketed and the compute bandit
    /// picks a `population_size` / `generations` multiplier.
    #[serde(default)]
    pub compute_directives: Vec<ComputeDirective>,
    /// LLM-driven self-curriculum status updates. Each entry
    /// transitions a previously-proposed target through the
    /// {open, proving, proved, abandoned} lifecycle. Empty by
    /// default; the LLM emits these as it reasons about progress.
    #[serde(default)]
    pub target_status_updates: Vec<TargetStatusUpdate>,
    /// Free-form pass-through field for forward compatibility with
    /// future LLM emission shapes. The current daemon stores this
    /// verbatim in `cluster_steering.config_json` and surfaces it
    /// back to the LLM in the next cycle's `history_newest_first`,
    /// so even without code changes the LLM can experiment with
    /// new directive shapes (e.g. multi-step proof plans, axiom
    /// dependency hints, novelty heuristics) and the system carries
    /// them forward as conversational state. When subsequent
    /// versions of the steerer / worker grow first-class support
    /// for a field that lives here, they can read it directly
    /// without breaking deserialisation of older configs. Bounded
    /// at ~16 KB by the LLM's max_tokens budget; nothing else
    /// validates it.
    #[serde(default)]
    #[schemars(skip)]
    pub extension: serde_json::Value,
    /// Indefinite-horizon LLM memory. The LLM rewrites this each
    /// cycle as a rolling summary of what worked, what didn't, and
    /// its current focus — replacing the previous version, not
    /// appending. Surfaced back into every future prompt as
    /// `previous_lessons_learned`, so insights survive past the
    /// 10-cycle `history_newest_first` window. Capped at 4000
    /// chars to keep the prompt budget bounded.
    #[serde(default)]
    pub lessons_learned: String,
    /// Free-form rationale (≤500 chars). Stored for the next cycle
    /// to read; never affects worker behaviour.
    pub rationale: String,
    /// LLM-curated physics-shape atoms per domain. Each domain maps to
    /// a list of stable atom names with selection weights; the GA's
    /// `random_physics_compound` sampler uses these (plus the
    /// hardcoded baseline of 8 SR/EM compounds) when present. Unknown
    /// atom names are silently dropped worker-side, so adding new
    /// atoms is forward-safe: the schema accepts them now; older
    /// workers ignore them; newer workers light them up the moment
    /// they ship. Empty/missing → uniform fallback to the baseline
    /// pool.
    ///
    /// Why this lever: progress.md iter 23-24 found that
    /// `append_productive_suffix` synthesises productive `X² = Y²`
    /// targets only when the random atoms include physics-shape
    /// compounds. The hardcoded 8-atom pool covers SR; EM, QM, GR each
    /// need their own. Letting the LLM (Kimi K2.6) propose the atom
    /// roster per domain replaces an engineer-tuned constant with a
    /// dynamic, history-aware curriculum.
    #[serde(default)]
    pub atom_pool: HashMap<String, Vec<AtomWeight>>,
}

/// One LLM-proposed atom for `random_physics_compound`. The `name`
/// is a stable handle the worker maps to an `Expr` tree; the
/// `weight` biases sampling within the pool. Weights are
/// normalised worker-side so the LLM doesn't need to keep them
/// summing to a constant.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, JsonSchema)]
pub struct AtomWeight {
    pub name: String,
    pub weight: f32,
}

/// Fitness shaping weights. The cluster's effective fitness is a
/// convex combination of these four components plus the dimensional
/// soundness gate.
#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, JsonSchema)]
pub struct FitnessWeights {
    pub novelty: f32,
    pub dimensional_elegance: f32,
    pub chain_length_penalty: f32,
    pub target_proximity: f32,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SoftTarget {
    pub latex: String,
    pub domain: String,
    pub weight: f32,
    /// Optional stable handle the LLM uses to track its self-curriculum
    /// proposals across cycles. When `Some`, the steerer cycle records
    /// the target in `llm_proposed_targets` and surfaces its lifecycle
    /// status in subsequent prompts. The LLM updates statuses via
    /// `target_status_updates` in subsequent emissions.
    #[serde(default)]
    pub target_id: Option<String>,
}

/// LLM-driven status update for a previously-proposed self-curriculum
/// target. Status transitions: open → proving → proved | abandoned.
/// The LLM judges progress by inspecting recent verified theorems in
/// the prompt; the server doesn't auto-detect proofs.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, JsonSchema)]
pub struct TargetStatusUpdate {
    pub target_id: String,
    pub new_status: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct HardTarget {
    pub latex: String,
    pub domain: String,
    pub weight: f32,
}

/// GA mutation knobs. Bounded so the steerer can't accidentally turn
/// the GA into pure random search (rate=1.0) or freeze it (rate=0.0).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, JsonSchema)]
pub struct MutationKnobs {
    /// Per-allele mutation probability. Bounded [0.05, 0.30].
    pub rate: f32,
    /// Bias toward end-of-chain mutations (good for "extending" a
    /// near-target chain). Bounded [0.0, 1.0].
    pub suffix_bias: f32,
    /// Population per island. Bounded [32, 512].
    pub population_size: u32,
    /// Fraction of best-fitness elites copied through. [0.0, 0.2].
    pub elitism_fraction: f32,
}

impl Default for MutationKnobs {
    fn default() -> Self {
        Self {
            rate: 0.10,
            suffix_bias: 0.4,
            population_size: 128,
            elitism_fraction: 0.05,
        }
    }
}

/// Test-time compute scaling directive. Distinct from
/// `cluster_directives` because compute is a chunk-wide knob, not
/// per-cluster. The LLM emits one per island it wants to scale
/// (Some(island_domain)) or one with `island_domain=None` to scale
/// every island uniformly. Strength is bucketed worker-side and the
/// compute bandit picks a population_size / generations multiplier
/// from the learned arm table — AlphaProof-style test-time-compute
/// scaling at the steering layer.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, JsonSchema)]
pub struct ComputeDirective {
    /// `None` = apply to every island; `Some(domain)` = scoped.
    pub island_domain: Option<String>,
    pub strength: f32,
}

/// Per-cluster directive emitted by the LLM. Addresses a cluster by
/// the `centroid_skeleton_hash` it observed in the previous chunk's
/// ClusterSummary, NOT by `cluster_id` — k-means renumbers clusters
/// every chunk so id-based addressing is unstable. Workers match by
/// minimum Hamming distance on the hash with a fixed threshold; if no
/// new cluster is close enough, the directive is silently dropped.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, JsonSchema)]
pub struct ClusterDirective {
    pub island_domain: String,
    pub centroid_skeleton_hash: u64,
    pub action: ClusterAction,
    /// [0.0, 1.0]; mapped to bounded multipliers worker-side. Strength
    /// 0 is a no-op; strength 1 is the maximum-magnitude effect.
    pub strength: f32,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum ClusterAction {
    /// Multiply per-individual mutation rate inside this cluster.
    Boost,
    /// Multiply elitism fraction inside this cluster (preserve more).
    Exploit,
    /// Re-seed the worst N% with random + axiom samples to escape a
    /// local optimum.
    Diversify,
    /// Drop a fraction of the cluster, refill from migrants.
    Kill,
}

#[derive(Debug, Error)]
pub enum SteeringValidationError {
    #[error("scope must be B or C, got {0}")]
    BadScope(String),
    #[error("domain_weights must sum to 1.0 (±0.01), got {0}")]
    DomainSum(f32),
    #[error("fitness_weights must sum to 1.0 (±0.01), got {0}")]
    FitnessSum(f32),
    #[error("axiom_emphasis values must be in [0.0, 2.0]")]
    BadEmphasis,
    #[error("mutation_priors values must be in [0.0, 2.0]")]
    BadMutationPrior,
    #[error("scope=B must have empty cluster_directives")]
    BHasClusterDirectives,
    #[error("cluster directive strength must be in [0.0, 1.0]")]
    BadDirectiveStrength,
    #[error("scope=B must have empty compute_directives")]
    BHasComputeDirectives,
    #[error("compute directive strength must be in [0.0, 1.0]")]
    BadComputeStrength,
    #[error("scope=B must have empty hard_targets")]
    BHasHardTargets,
    #[error("scope=B must have null mutation_knobs")]
    BHasMutationKnobs,
    #[error("mutation_knobs.{field} out of range")]
    KnobRange { field: &'static str },
    #[error("rationale exceeds 500 chars")]
    RationaleTooLong,
    #[error("lessons_learned exceeds 4000 chars")]
    LessonsTooLong,
    #[error("atom_pool weights must be finite and in [0.0, 4.0]")]
    BadAtomWeight,
}

impl SteeringConfig {
    pub fn validate(&self) -> Result<(), SteeringValidationError> {
        if self.scope != "B" && self.scope != "C" {
            return Err(SteeringValidationError::BadScope(self.scope.clone()));
        }
        let dsum: f32 = self.domain_weights.values().sum();
        if (dsum - 1.0).abs() > 0.01 {
            return Err(SteeringValidationError::DomainSum(dsum));
        }
        let fsum = self.fitness_weights.novelty
            + self.fitness_weights.dimensional_elegance
            + self.fitness_weights.chain_length_penalty
            + self.fitness_weights.target_proximity;
        if (fsum - 1.0).abs() > 0.01 {
            return Err(SteeringValidationError::FitnessSum(fsum));
        }
        if self
            .axiom_emphasis
            .values()
            .any(|v| !(0.0..=2.0).contains(v))
        {
            return Err(SteeringValidationError::BadEmphasis);
        }
        if self
            .mutation_priors
            .values()
            .any(|v| !(0.0..=2.0).contains(v))
        {
            return Err(SteeringValidationError::BadMutationPrior);
        }
        if self.scope == "B" {
            if !self.hard_targets.is_empty() {
                return Err(SteeringValidationError::BHasHardTargets);
            }
            if self.mutation_knobs.is_some() {
                return Err(SteeringValidationError::BHasMutationKnobs);
            }
            if !self.cluster_directives.is_empty() {
                return Err(SteeringValidationError::BHasClusterDirectives);
            }
            if !self.compute_directives.is_empty() {
                return Err(SteeringValidationError::BHasComputeDirectives);
            }
        }
        for d in &self.cluster_directives {
            if !(0.0..=1.0).contains(&d.strength) {
                return Err(SteeringValidationError::BadDirectiveStrength);
            }
        }
        for d in &self.compute_directives {
            if !(0.0..=1.0).contains(&d.strength) {
                return Err(SteeringValidationError::BadComputeStrength);
            }
        }
        if let Some(k) = &self.mutation_knobs {
            if !(0.05..=0.30).contains(&k.rate) {
                return Err(SteeringValidationError::KnobRange { field: "rate" });
            }
            if !(0.0..=1.0).contains(&k.suffix_bias) {
                return Err(SteeringValidationError::KnobRange {
                    field: "suffix_bias",
                });
            }
            if !(32..=512).contains(&k.population_size) {
                return Err(SteeringValidationError::KnobRange {
                    field: "population_size",
                });
            }
            if !(0.0..=0.2).contains(&k.elitism_fraction) {
                return Err(SteeringValidationError::KnobRange {
                    field: "elitism_fraction",
                });
            }
        }
        if self.rationale.chars().count() > 500 {
            return Err(SteeringValidationError::RationaleTooLong);
        }
        if self.lessons_learned.chars().count() > 4000 {
            return Err(SteeringValidationError::LessonsTooLong);
        }
        for atoms in self.atom_pool.values() {
            for a in atoms {
                if !a.weight.is_finite() || !(0.0..=4.0).contains(&a.weight) {
                    return Err(SteeringValidationError::BadAtomWeight);
                }
            }
        }
        Ok(())
    }
}

/// Cold-start config used when there is no history yet (first ever
/// cycle, or the steerer is disabled). Even spread across the four
/// supported domains, default mutation knobs.
pub fn default_config() -> SteeringConfig {
    let mut domain_weights = HashMap::new();
    domain_weights.insert("special_relativity".into(), 0.25);
    domain_weights.insert("electromagnetism".into(), 0.25);
    domain_weights.insert("classical_mechanics".into(), 0.25);
    domain_weights.insert("thermodynamics".into(), 0.25);
    SteeringConfig {
        version: 1,
        scope: "C".into(),
        domain_weights,
        axiom_emphasis: HashMap::new(),
        fitness_weights: FitnessWeights {
            novelty: 0.4,
            dimensional_elegance: 0.3,
            chain_length_penalty: 0.2,
            target_proximity: 0.1,
        },
        soft_targets: vec![],
        hard_targets: vec![],
        mutation_knobs: Some(MutationKnobs::default()),
        mutation_priors: HashMap::new(),
        cluster_directives: vec![],
        compute_directives: vec![],
        target_status_updates: vec![],
        extension: serde_json::Value::Null,
        lessons_learned: String::new(),
        rationale: "default cold-start config".into(),
        atom_pool: HashMap::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_passes_validation() {
        default_config().validate().unwrap();
    }

    #[test]
    fn domain_weights_must_sum_to_one() {
        let mut c = default_config();
        c.domain_weights
            .insert("special_relativity".into(), 0.3);
        // Now sums to 0.3 + 0.25 + 0.25 + 0.25 = 1.05, outside ±0.01
        assert!(c.validate().is_err());
    }

    #[test]
    fn mode_b_rejects_mutation_knobs() {
        let mut c = default_config();
        c.scope = "B".into();
        // mutation_knobs is Some by default; B must have None.
        assert!(matches!(
            c.validate(),
            Err(SteeringValidationError::BHasMutationKnobs)
        ));
    }

    #[test]
    fn mode_b_rejects_hard_targets() {
        let mut c = default_config();
        c.scope = "B".into();
        c.mutation_knobs = None;
        c.hard_targets.push(HardTarget {
            latex: "x=y".into(),
            domain: "sr".into(),
            weight: 0.5,
        });
        assert!(matches!(
            c.validate(),
            Err(SteeringValidationError::BHasHardTargets)
        ));
    }

    #[test]
    fn fitness_weights_must_sum_to_one() {
        let mut c = default_config();
        c.fitness_weights.novelty = 2.0;
        assert!(c.validate().is_err());
    }

    #[test]
    fn axiom_emphasis_clamped_to_two() {
        let mut c = default_config();
        c.axiom_emphasis.insert("foo".into(), 2.5);
        assert!(matches!(
            c.validate(),
            Err(SteeringValidationError::BadEmphasis)
        ));
    }

    #[test]
    fn knobs_out_of_range_rejected() {
        let mut c = default_config();
        c.mutation_knobs = Some(MutationKnobs {
            rate: 0.5,
            ..MutationKnobs::default()
        });
        assert!(c.validate().is_err());
    }

    #[test]
    fn mutation_priors_round_trip() {
        let mut c = default_config();
        c.mutation_priors
            .insert("append_productive_suffix".into(), 1.5);
        c.mutation_priors.insert("mutate_axiom_name".into(), 0.5);
        let json = serde_json::to_string(&c).unwrap();
        let parsed: SteeringConfig = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.mutation_priors.len(), 2);
        parsed.validate().unwrap();
    }

    #[test]
    fn mutation_priors_value_above_2_rejected() {
        let mut c = default_config();
        c.mutation_priors.insert("insert_random".into(), 2.5);
        assert!(matches!(
            c.validate(),
            Err(SteeringValidationError::BadMutationPrior)
        ));
    }

    #[test]
    fn mutation_priors_negative_rejected() {
        let mut c = default_config();
        c.mutation_priors.insert("insert_random".into(), -0.1);
        assert!(c.validate().is_err());
    }

    #[test]
    fn cluster_directive_round_trip() {
        let mut c = default_config();
        c.cluster_directives.push(ClusterDirective {
            island_domain: "special_relativity".into(),
            centroid_skeleton_hash: 0xdead_beef_cafe_babe,
            action: ClusterAction::Boost,
            strength: 0.5,
        });
        let json = serde_json::to_string(&c).unwrap();
        let parsed: SteeringConfig = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.cluster_directives.len(), 1);
        assert_eq!(parsed.cluster_directives[0].action, ClusterAction::Boost);
        parsed.validate().unwrap();
    }

    #[test]
    fn mode_b_rejects_cluster_directives() {
        let mut c = default_config();
        c.scope = "B".into();
        c.mutation_knobs = None;
        c.cluster_directives.push(ClusterDirective {
            island_domain: "x".into(),
            centroid_skeleton_hash: 0,
            action: ClusterAction::Kill,
            strength: 1.0,
        });
        assert!(matches!(
            c.validate(),
            Err(SteeringValidationError::BHasClusterDirectives)
        ));
    }

    #[test]
    fn directive_strength_above_one_rejected() {
        let mut c = default_config();
        c.cluster_directives.push(ClusterDirective {
            island_domain: "x".into(),
            centroid_skeleton_hash: 0,
            action: ClusterAction::Diversify,
            strength: 1.5,
        });
        assert!(c.validate().is_err());
    }

    #[test]
    fn default_has_empty_lessons_learned() {
        let c = default_config();
        assert!(c.lessons_learned.is_empty());
        c.validate().unwrap();
    }

    #[test]
    fn lessons_learned_under_cap_validates() {
        let mut c = default_config();
        c.lessons_learned = "a".repeat(4000);
        c.validate().unwrap();
    }

    #[test]
    fn lessons_learned_over_cap_rejected() {
        let mut c = default_config();
        c.lessons_learned = "a".repeat(4001);
        assert!(matches!(
            c.validate(),
            Err(SteeringValidationError::LessonsTooLong)
        ));
    }

    #[test]
    fn lessons_learned_serde_round_trip() {
        let mut c = default_config();
        c.lessons_learned =
            "Boost@SR strength=0.5 → 1.5× has worked. Diversify in QM has not.".into();
        let json = serde_json::to_string(&c).unwrap();
        let parsed: SteeringConfig = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.lessons_learned, c.lessons_learned);
        parsed.validate().unwrap();
    }

    #[test]
    fn lessons_learned_missing_field_deserialises_to_empty() {
        // Backwards compat: an old serialised config without
        // lessons_learned should still parse + validate.
        let cfg = default_config();
        let mut value = serde_json::to_value(&cfg).unwrap();
        value
            .as_object_mut()
            .unwrap()
            .remove("lessons_learned");
        let parsed: SteeringConfig = serde_json::from_value(value).unwrap();
        assert!(parsed.lessons_learned.is_empty());
        parsed.validate().unwrap();
    }

    #[test]
    fn atom_pool_round_trip() {
        let mut c = default_config();
        c.atom_pool.insert(
            "special_relativity".into(),
            vec![
                AtomWeight { name: "m_c_sq".into(), weight: 1.5 },
                AtomWeight { name: "e_sq".into(), weight: 1.0 },
            ],
        );
        c.atom_pool.insert(
            "quantum_mechanics".into(),
            vec![AtomWeight { name: "hbar_omega".into(), weight: 2.0 }],
        );
        let json = serde_json::to_string(&c).unwrap();
        let parsed: SteeringConfig = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.atom_pool.len(), 2);
        assert_eq!(parsed.atom_pool["special_relativity"].len(), 2);
        parsed.validate().unwrap();
    }

    #[test]
    fn atom_pool_weight_above_four_rejected() {
        let mut c = default_config();
        c.atom_pool.insert(
            "sr".into(),
            vec![AtomWeight { name: "x".into(), weight: 5.0 }],
        );
        assert!(matches!(
            c.validate(),
            Err(SteeringValidationError::BadAtomWeight)
        ));
    }

    #[test]
    fn atom_pool_nan_weight_rejected() {
        let mut c = default_config();
        c.atom_pool.insert(
            "sr".into(),
            vec![AtomWeight { name: "x".into(), weight: f32::NAN }],
        );
        assert!(matches!(
            c.validate(),
            Err(SteeringValidationError::BadAtomWeight)
        ));
    }

    #[test]
    fn atom_pool_missing_field_deserialises_to_empty() {
        let cfg = default_config();
        let mut value = serde_json::to_value(&cfg).unwrap();
        value.as_object_mut().unwrap().remove("atom_pool");
        let parsed: SteeringConfig = serde_json::from_value(value).unwrap();
        assert!(parsed.atom_pool.is_empty());
        parsed.validate().unwrap();
    }
}
