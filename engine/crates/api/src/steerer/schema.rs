//! `SteeringConfig` — the contract between the cluster steerer and
//! every worker.
//!
//! Every cycle the LLM emits one of these. The validator rejects any
//! out-of-range value so a bad model response never poisons the
//! cluster (cycle.rs falls back to the last-known-good config). The
//! schema deliberately constrains all numeric ranges so a small model
//! that forgot a constraint emits something rejectable rather than
//! something that quietly causes drift.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use thiserror::Error;

/// Top-level steering payload. Workers read `mutation_knobs` and the
/// fitness weights every chunk; targets and emphasis affect chain
/// composition and seed selection.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
    /// Free-form rationale (≤500 chars). Stored for the next cycle
    /// to read; never affects worker behaviour.
    pub rationale: String,
}

/// Fitness shaping weights. The cluster's effective fitness is a
/// convex combination of these four components plus the dimensional
/// soundness gate.
#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq)]
pub struct FitnessWeights {
    pub novelty: f32,
    pub dimensional_elegance: f32,
    pub chain_length_penalty: f32,
    pub target_proximity: f32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SoftTarget {
    pub latex: String,
    pub domain: String,
    pub weight: f32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HardTarget {
    pub latex: String,
    pub domain: String,
    pub weight: f32,
}

/// GA mutation knobs. Bounded so the steerer can't accidentally turn
/// the GA into pure random search (rate=1.0) or freeze it (rate=0.0).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
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

/// Per-cluster directive emitted by the LLM. Addresses a cluster by
/// the `centroid_skeleton_hash` it observed in the previous chunk's
/// ClusterSummary, NOT by `cluster_id` — k-means renumbers clusters
/// every chunk so id-based addressing is unstable. Workers match by
/// minimum Hamming distance on the hash with a fixed threshold; if no
/// new cluster is close enough, the directive is silently dropped.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ClusterDirective {
    pub island_domain: String,
    pub centroid_skeleton_hash: u64,
    pub action: ClusterAction,
    /// [0.0, 1.0]; mapped to bounded multipliers worker-side. Strength
    /// 0 is a no-op; strength 1 is the maximum-magnitude effect.
    pub strength: f32,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
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
    #[error("scope=B must have empty hard_targets")]
    BHasHardTargets,
    #[error("scope=B must have null mutation_knobs")]
    BHasMutationKnobs,
    #[error("mutation_knobs.{field} out of range")]
    KnobRange { field: &'static str },
    #[error("rationale exceeds 500 chars")]
    RationaleTooLong,
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
        }
        for d in &self.cluster_directives {
            if !(0.0..=1.0).contains(&d.strength) {
                return Err(SteeringValidationError::BadDirectiveStrength);
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
        rationale: "default cold-start config".into(),
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
}
