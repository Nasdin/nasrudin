//! Genotype-level clustering inside an island.
//!
//! Used by the LLM cluster steerer to address sub-populations by their
//! `centroid_skeleton_hash` and apply per-cluster directives (Boost,
//! Exploit, Diversify, Kill).
//!
//! K is supplied externally by the API steerer's UCB1 bandit; this
//! module does not pick K itself.

pub mod features;
pub mod kmeans;
pub mod summary;

pub use features::{signature_distance, ClusterFeatures, MINHASH_SIG_LEN};
pub use kmeans::{cluster_individuals, Centroid, ClusterAssignment};
pub use summary::{compute_summaries, ClusterSummary};

use nasrudin_derive::{Chain, RuleStep};
use serde::{Deserialize, Serialize};

/// Per-directive bookkeeping kept worker-local across a single chunk
/// boundary. At chunk N the worker applies the directive and records
/// this entry; at chunk N+1, after re-clustering, the worker matches
/// `centroid_hash_at_apply` against the new clusters and emits reward
/// feedback if a current cluster is within Hamming threshold.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkerDirectiveEntry {
    pub centroid_hash_at_apply: u64,
    pub action: String,
    pub strength_bucket: u8,
    pub multiplier_choice: u8,
    pub mean_fitness_at_apply: f32,
}

/// Discount factor for the eligibility trace's discounted-return
/// computation. 0.7 is a moderate decay — sample at chunk N+0 is
/// fully credited, N+1 at 70%, N+2 at 49%. Lower γ would make the
/// bandit more myopic; higher would over-credit late chunks where
/// cluster identity has drifted further.
pub const TRACE_GAMMA: f64 = 0.7;

/// Number of chunks an eligibility trace stays in flight. After
/// `TRACE_HORIZON` samples (one per chunk including the apply
/// chunk), the trace's discounted return is computed and posted to
/// the bandit. Higher horizons trade off responsiveness for
/// stability of the reward signal.
pub const TRACE_HORIZON: u8 = 3;

/// In-flight eligibility trace for one applied directive. Replaces
/// the single-shot `WorkerDirectiveEntry` reward path: instead of
/// posting at chunk N+1, the worker keeps the trace alive for
/// `TRACE_HORIZON` chunks, accumulating per-chunk samples (matched
/// by `centroid_hash_at_apply`) and emitting a γ-discounted return.
///
/// `samples[0]` is observed at the same chunk the directive lands
/// (computed from the final population grouped by lineage cluster_id).
/// Subsequent `samples[t]` are observed at chunks N+t via Hamming
/// hash matching against the new chunk's clusters.
#[derive(Debug, Clone)]
pub struct DirectiveTrace {
    pub centroid_hash_at_apply: u64,
    pub action: String,
    pub strength_bucket: u8,
    pub multiplier_choice: u8,
    pub mean_fitness_at_apply: f32,
    pub samples: Vec<f32>,
    pub chunks_remaining: u8,
}

impl DirectiveTrace {
    pub fn new(
        centroid_hash_at_apply: u64,
        action: String,
        strength_bucket: u8,
        multiplier_choice: u8,
        mean_fitness_at_apply: f32,
    ) -> Self {
        Self {
            centroid_hash_at_apply,
            action,
            strength_bucket,
            multiplier_choice,
            mean_fitness_at_apply,
            samples: Vec::new(),
            chunks_remaining: TRACE_HORIZON,
        }
    }

    /// Compute the γ-discounted normalised return from accumulated
    /// samples. Returns the bandit reward signal mapped into [0, 1]
    /// via the same affine bias the single-shot path used.
    ///
    /// Empty `samples` → 0.5 (neutral); the trace was abandoned
    /// without observing anything.
    pub fn discounted_reward(&self) -> f64 {
        if self.samples.is_empty() {
            return 0.5;
        }
        let mut total = 0.0f64;
        let mut weight_sum = 0.0f64;
        for (t, s) in self.samples.iter().enumerate() {
            let w = TRACE_GAMMA.powi(t as i32);
            total += w * (*s - self.mean_fitness_at_apply) as f64;
            weight_sum += w;
        }
        let normalized = if weight_sum > 0.0 {
            total / weight_sum
        } else {
            0.0
        };
        (normalized + 0.5).clamp(0.0, 1.0)
    }
}

/// One-shot helper: feature-extract → k-means → summarise.
///
/// `chains_with_fitness` is `(chain, fitness_components, axiom_names)`
/// per individual. `axiom_names` is pre-extracted (caller already has
/// the chain in scope) so the summary can report dominant axioms
/// without re-walking each chain.
///
/// Returns `(summaries, assignment)` so callers can both upload
/// summaries and apply per-cluster directives in the same chunk.
pub fn cluster_and_summarise(
    chains_with_fitness: &[(Chain, [f32; 4], Vec<String>)],
    k: u32,
    island_domain: &str,
    seed: u64,
) -> (Vec<ClusterSummary>, ClusterAssignment) {
    let features: Vec<ClusterFeatures> = chains_with_fitness
        .iter()
        .map(|(c, f, _)| ClusterFeatures::from_chain(c, f))
        .collect();
    let axiom_names: Vec<Vec<String>> = chains_with_fitness
        .iter()
        .map(|(_, _, names)| names.clone())
        .collect();
    let asg = cluster_individuals(&features, k, seed);
    let summaries = compute_summaries(&features, &asg, &axiom_names, island_domain);
    (summaries, asg)
}

/// Extract the axiom / theorem names referenced by a chain. Used to
/// build the `dominant_axioms` field on each `ClusterSummary` and to
/// avoid the chain having to be re-walked downstream.
pub fn extract_axiom_names(chain: &Chain) -> Vec<String> {
    chain
        .0
        .iter()
        .filter_map(|step| match step {
            RuleStep::IntroduceAxiom { axiom_name } => Some(axiom_name.clone()),
            RuleStep::IntroduceTheorem { theorem_name } => Some(theorem_name.clone()),
            _ => None,
        })
        .collect()
}

/// Match a directive's `centroid_skeleton_hash` to the closest cluster
/// in the new chunk. `cluster_centroids` is `[(cluster_id, hash)]`.
/// Returns `Some(cluster_id)` if the closest is within
/// `max_normalised_hamming` (Hamming over 64 bits / 64.0). Otherwise
/// `None` — the directive is silently dropped because cluster identity
/// drifted too far between chunks.
pub fn match_directive_to_cluster(
    directive_hash: u64,
    cluster_centroids: &[(u32, u64)],
    max_normalised_hamming: f32,
) -> Option<u32> {
    let mut best: Option<(u32, f32)> = None;
    for &(cid, h) in cluster_centroids {
        let d = (directive_hash ^ h).count_ones() as f32 / 64.0;
        if d <= max_normalised_hamming && best.is_none_or(|(_, bd)| d < bd) {
            best = Some((cid, d));
        }
    }
    best.map(|(cid, _)| cid)
}

#[cfg(test)]
mod directive_tests {
    use super::*;

    #[test]
    fn match_by_hash_finds_closest_centroid() {
        let centroids = vec![
            (0u32, 0xAAAA_AAAA_AAAA_AAAAu64),
            (1u32, 0x5555_5555_5555_5555u64),
        ];
        let m = match_directive_to_cluster(0xAAAA_AAAA_AAAA_AAAA, &centroids, 0.10);
        assert_eq!(m, Some(0));
    }

    #[test]
    fn match_by_hash_drops_when_no_close_match() {
        let centroids = vec![(0u32, 0xAAAA_AAAA_AAAA_AAAAu64)];
        // Complement → max distance 1.0; threshold 0.10 → drop.
        let m = match_directive_to_cluster(0x5555_5555_5555_5555, &centroids, 0.10);
        assert_eq!(m, None);
    }

    #[test]
    fn match_by_hash_picks_minimum_distance_among_close_options() {
        let centroids = vec![
            (0u32, 0xAAAA_AAAA_AAAA_AAAAu64),
            (1u32, 0xAAAA_AAAA_AAAA_AAABu64), // 1 bit away
            (2u32, 0xAAAA_AAAA_AAAA_AAAFu64), // 3 bits away
        ];
        let m = match_directive_to_cluster(0xAAAA_AAAA_AAAA_AAAA, &centroids, 0.10);
        assert_eq!(m, Some(0));
    }

    #[test]
    fn worker_directive_entry_round_trips_basic_fields() {
        let e = WorkerDirectiveEntry {
            centroid_hash_at_apply: 0xdead_beef_cafe_babe,
            action: "boost".into(),
            strength_bucket: 2,
            multiplier_choice: 3,
            mean_fitness_at_apply: 0.42,
        };
        let json = serde_json::to_string(&e).unwrap();
        let parsed: WorkerDirectiveEntry = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.action, "boost");
        assert_eq!(parsed.strength_bucket, 2);
        assert_eq!(parsed.multiplier_choice, 3);
        assert!((parsed.mean_fitness_at_apply - 0.42).abs() < 1e-6);
    }

    #[test]
    fn trace_empty_samples_returns_neutral_reward() {
        let t = DirectiveTrace::new(0, "boost".into(), 2, 3, 0.5);
        assert!((t.discounted_reward() - 0.5).abs() < 1e-9);
    }

    #[test]
    fn trace_discounted_reward_weights_recent_samples_more() {
        // apply_mean=0.0, samples=[0.5, 0.5, 0.5] → constant +0.5 delta
        // Discounted normalised return = 0.5 → reward = 0.5 + 0.5 = 1.0 (clamped)
        let mut t = DirectiveTrace::new(0, "boost".into(), 2, 3, 0.0);
        t.samples = vec![0.5, 0.5, 0.5];
        let r = t.discounted_reward();
        assert!((r - 1.0).abs() < 1e-9);
    }

    #[test]
    fn trace_normalises_uneven_lengths() {
        // Single sample +0.3 → normalised = 0.3 → reward = 0.8
        let mut t = DirectiveTrace::new(0, "boost".into(), 2, 3, 0.0);
        t.samples = vec![0.3];
        let r = t.discounted_reward();
        assert!((r - 0.8).abs() < 1e-6);
    }

    #[test]
    fn trace_clamps_extreme_values() {
        let mut t = DirectiveTrace::new(0, "boost".into(), 2, 3, 0.0);
        t.samples = vec![5.0, 5.0, 5.0];
        assert_eq!(t.discounted_reward(), 1.0);
        let mut t2 = DirectiveTrace::new(0, "boost".into(), 2, 3, 0.0);
        t2.samples = vec![-5.0, -5.0, -5.0];
        assert_eq!(t2.discounted_reward(), 0.0);
    }
}
