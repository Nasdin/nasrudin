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
}
