//! Per-cluster summary uploaded to the API after every chunk.

use crate::clustering::features::{signature_distance, ClusterFeatures};
use crate::clustering::kmeans::ClusterAssignment;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClusterSummary {
    pub cluster_id: u32,
    pub island_domain: String,
    pub size: u32,
    pub mean_fitness: f32,
    pub fitness_stddev: f32,
    pub silhouette: f32,
    pub dominant_axioms: Vec<(String, u32)>,
    /// Filled in by the API steerer using historical reports;
    /// workers always send 0.0.
    pub novelty_trend: f32,
    /// Filled in by the API steerer; workers always send 0.
    pub stagnation_chunks: u32,
    pub centroid_skeleton_hash: u64,
}

pub fn compute_summaries(
    population: &[ClusterFeatures],
    assignment: &ClusterAssignment,
    axiom_names_per_individual: &[Vec<String>],
    island_domain: &str,
) -> Vec<ClusterSummary> {
    if population.is_empty() {
        return vec![];
    }
    let k = assignment.centroids.len();
    let mut out = Vec::with_capacity(k);
    for cid in 0..k {
        let member_idxs: Vec<usize> = assignment
            .assignments
            .iter()
            .enumerate()
            .filter(|&(_, &c)| c == cid as u32)
            .map(|(i, _)| i)
            .collect();
        if member_idxs.is_empty() {
            continue;
        }
        let fits: Vec<f32> = member_idxs
            .iter()
            .map(|&i| population[i].fitness_components.iter().sum::<f32>() / 4.0)
            .collect();
        let mean = fits.iter().sum::<f32>() / fits.len() as f32;
        let var = fits.iter().map(|f| (f - mean).powi(2)).sum::<f32>() / fits.len() as f32;

        let mut axiom_counts: HashMap<String, u32> = HashMap::new();
        for &i in &member_idxs {
            for name in &axiom_names_per_individual[i] {
                *axiom_counts.entry(name.clone()).or_insert(0) += 1;
            }
        }
        let mut dominant: Vec<(String, u32)> = axiom_counts.into_iter().collect();
        dominant.sort_by(|a, b| b.1.cmp(&a.1));
        dominant.truncate(5);

        let c = &assignment.centroids[cid];
        let centroid_skeleton_hash = xxhash_rust::xxh64::xxh64(&c.axiom_signature, 0);

        out.push(ClusterSummary {
            cluster_id: cid as u32,
            island_domain: island_domain.into(),
            size: member_idxs.len() as u32,
            mean_fitness: mean,
            fitness_stddev: var.sqrt(),
            silhouette: silhouette_score(population, assignment, &member_idxs, cid as u32),
            dominant_axioms: dominant,
            novelty_trend: 0.0,
            stagnation_chunks: 0,
            centroid_skeleton_hash,
        });
    }
    out
}

/// Standard silhouette score over the axiom-usage signature distance.
/// Returns the mean over members; bounded to `[-1, 1]`. Returns 0.0
/// for trivial clusters (single member or single cluster).
fn silhouette_score(
    population: &[ClusterFeatures],
    assignment: &ClusterAssignment,
    members: &[usize],
    own: u32,
) -> f32 {
    if members.len() < 2 || assignment.centroids.len() < 2 {
        return 0.0;
    }
    let mut total = 0.0f32;
    let mut counted = 0u32;
    for &i in members {
        let same: Vec<f32> = members
            .iter()
            .filter(|&&j| j != i)
            .map(|&j| {
                signature_distance(
                    &population[i].axiom_usage_signature,
                    &population[j].axiom_usage_signature,
                )
            })
            .collect();
        if same.is_empty() {
            continue;
        }
        let a: f32 = same.iter().sum::<f32>() / same.len() as f32;
        let mut b = f32::INFINITY;
        for cid in 0..assignment.centroids.len() {
            if cid as u32 == own {
                continue;
            }
            let other_members: Vec<usize> = assignment
                .assignments
                .iter()
                .enumerate()
                .filter(|&(_, &c)| c == cid as u32)
                .map(|(j, _)| j)
                .collect();
            if other_members.is_empty() {
                continue;
            }
            let mean: f32 = other_members
                .iter()
                .map(|&j| {
                    signature_distance(
                        &population[i].axiom_usage_signature,
                        &population[j].axiom_usage_signature,
                    )
                })
                .sum::<f32>()
                / other_members.len() as f32;
            if mean < b {
                b = mean;
            }
        }
        if b.is_finite() {
            total += (b - a) / a.max(b).max(1e-6);
            counted += 1;
        }
    }
    if counted == 0 {
        0.0
    } else {
        total / counted as f32
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clustering::features::MINHASH_SIG_LEN;
    use crate::clustering::kmeans::Centroid;

    fn assignment_of(labels: &[u32], k: u32) -> ClusterAssignment {
        let centroids = (0..k)
            .map(|_| Centroid {
                axiom_signature: [0; MINHASH_SIG_LEN],
                op_skeleton: [0.0; 6],
                fitness_components: [0.0; 4],
            })
            .collect();
        ClusterAssignment {
            assignments: labels.to_vec(),
            centroids,
        }
    }

    #[test]
    fn summary_reports_correct_size() {
        let pop: Vec<_> = (0..6)
            .map(|_| ClusterFeatures {
                axiom_usage_signature: [0; MINHASH_SIG_LEN],
                op_skeleton: [0; 6],
                fitness_components: [0.5; 4],
            })
            .collect();
        let asg = assignment_of(&[0, 0, 0, 1, 1, 1], 2);
        let names: Vec<Vec<String>> = vec![vec![]; 6];
        let summaries = compute_summaries(&pop, &asg, &names, "special_relativity");
        assert_eq!(summaries.len(), 2);
        assert!(summaries.iter().all(|s| s.size == 3));
        assert!(summaries
            .iter()
            .all(|s| s.island_domain == "special_relativity"));
    }

    #[test]
    fn dominant_axioms_ordered_by_frequency() {
        let pop: Vec<_> = (0..3)
            .map(|_| ClusterFeatures {
                axiom_usage_signature: [0; MINHASH_SIG_LEN],
                op_skeleton: [0; 6],
                fitness_components: [0.0; 4],
            })
            .collect();
        let asg = assignment_of(&[0, 0, 0], 1);
        let names = vec![
            vec!["lorentz_factor".into(), "minkowski".into()],
            vec!["lorentz_factor".into()],
            vec!["lorentz_factor".into(), "minkowski".into()],
        ];
        let s = compute_summaries(&pop, &asg, &names, "sr");
        assert_eq!(s.len(), 1);
        // lorentz_factor (3) before minkowski (2)
        assert_eq!(s[0].dominant_axioms[0].0, "lorentz_factor");
        assert_eq!(s[0].dominant_axioms[0].1, 3);
        assert_eq!(s[0].dominant_axioms[1].0, "minkowski");
        assert_eq!(s[0].dominant_axioms[1].1, 2);
    }

    #[test]
    fn empty_cluster_skipped() {
        let pop: Vec<_> = (0..3)
            .map(|_| ClusterFeatures {
                axiom_usage_signature: [0; MINHASH_SIG_LEN],
                op_skeleton: [0; 6],
                fitness_components: [0.0; 4],
            })
            .collect();
        // K=3 but all assigned to cluster 0
        let asg = assignment_of(&[0, 0, 0], 3);
        let names: Vec<Vec<String>> = vec![vec![]; 3];
        let s = compute_summaries(&pop, &asg, &names, "sr");
        assert_eq!(s.len(), 1, "empty clusters should be skipped");
        assert_eq!(s[0].size, 3);
    }
}
