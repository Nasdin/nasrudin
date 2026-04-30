//! K-means++ over `ClusterFeatures` with deterministic seeding.

use crate::clustering::features::{signature_distance, ClusterFeatures, MINHASH_SIG_LEN};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

const MAX_ITERS: usize = 20;

#[derive(Debug, Clone)]
pub struct ClusterAssignment {
    /// Index → cluster id.
    pub assignments: Vec<u32>,
    pub centroids: Vec<Centroid>,
}

#[derive(Debug, Clone)]
pub struct Centroid {
    pub axiom_signature: [u8; MINHASH_SIG_LEN],
    pub op_skeleton: [f32; 6],
    pub fitness_components: [f32; 4],
}

/// Cluster `population` into `k` groups using K-means++. Deterministic
/// for a fixed `seed`. Returns assignments + final centroids.
///
/// `k` is clamped to `[1, population.len()]`. Empty population →
/// empty assignment with one sentinel centroid.
pub fn cluster_individuals(
    population: &[ClusterFeatures],
    k: u32,
    seed: u64,
) -> ClusterAssignment {
    if population.is_empty() {
        return ClusterAssignment {
            assignments: vec![],
            centroids: vec![Centroid {
                axiom_signature: [0xFF; MINHASH_SIG_LEN],
                op_skeleton: [0.0; 6],
                fitness_components: [0.0; 4],
            }],
        };
    }
    let k = (k as usize).clamp(1, population.len());
    let mut rng = StdRng::seed_from_u64(seed);

    // K-means++ seeding: first centroid uniform, subsequent ones
    // proportional to squared distance from nearest existing centroid.
    let mut centroid_idxs: Vec<usize> = vec![rng.random_range(0..population.len())];
    while centroid_idxs.len() < k {
        let weights: Vec<f32> = population
            .iter()
            .enumerate()
            .map(|(i, p)| {
                if centroid_idxs.contains(&i) {
                    return 0.0;
                }
                let min_d = centroid_idxs
                    .iter()
                    .map(|&ci| distance(p, &population[ci]))
                    .fold(f32::INFINITY, f32::min);
                min_d * min_d
            })
            .collect();
        let sum: f32 = weights.iter().sum();
        if sum <= 0.0 {
            break; // Degenerate: all points are duplicates of existing centroids.
        }
        let pick = weighted_choice(&weights, sum, &mut rng);
        centroid_idxs.push(pick);
    }

    let mut centroids: Vec<Centroid> = centroid_idxs
        .iter()
        .map(|&i| Centroid {
            axiom_signature: population[i].axiom_usage_signature,
            op_skeleton: population[i].op_skeleton.map(|v| v as f32),
            fitness_components: population[i].fitness_components,
        })
        .collect();

    let mut assignments = vec![0u32; population.len()];
    for _iter in 0..MAX_ITERS {
        let mut changed = false;
        for (i, p) in population.iter().enumerate() {
            let mut best = 0usize;
            let mut best_d = f32::INFINITY;
            for (ci, c) in centroids.iter().enumerate() {
                let d = distance_to_centroid(p, c);
                if d < best_d {
                    best_d = d;
                    best = ci;
                }
            }
            if assignments[i] != best as u32 {
                assignments[i] = best as u32;
                changed = true;
            }
        }
        if !changed {
            break;
        }
        // Update step: per-byte median of signature, mean of numeric components.
        for (ci, c) in centroids.iter_mut().enumerate() {
            let members: Vec<&ClusterFeatures> = population
                .iter()
                .enumerate()
                .filter(|(i, _)| assignments[*i] == ci as u32)
                .map(|(_, p)| p)
                .collect();
            if members.is_empty() {
                continue;
            }
            for byte_i in 0..MINHASH_SIG_LEN {
                let mut bytes: Vec<u8> = members
                    .iter()
                    .map(|m| m.axiom_usage_signature[byte_i])
                    .collect();
                bytes.sort_unstable();
                c.axiom_signature[byte_i] = bytes[bytes.len() / 2];
            }
            for op_i in 0..6 {
                let s: u32 = members.iter().map(|m| m.op_skeleton[op_i]).sum();
                c.op_skeleton[op_i] = s as f32 / members.len() as f32;
            }
            for f_i in 0..4 {
                let s: f32 = members.iter().map(|m| m.fitness_components[f_i]).sum();
                c.fitness_components[f_i] = s / members.len() as f32;
            }
        }
    }
    ClusterAssignment {
        assignments,
        centroids,
    }
}

fn distance(a: &ClusterFeatures, b: &ClusterFeatures) -> f32 {
    let sig = signature_distance(&a.axiom_usage_signature, &b.axiom_usage_signature);
    let op = op_distance(
        &a.op_skeleton.map(|v| v as f32),
        &b.op_skeleton.map(|v| v as f32),
    );
    let fit = fitness_distance(&a.fitness_components, &b.fitness_components);
    (0.5 * sig * sig + 0.3 * op * op + 0.2 * fit * fit).sqrt()
}

fn distance_to_centroid(p: &ClusterFeatures, c: &Centroid) -> f32 {
    let sig = signature_distance(&p.axiom_usage_signature, &c.axiom_signature);
    let op = op_distance(&p.op_skeleton.map(|v| v as f32), &c.op_skeleton);
    let fit = fitness_distance(&p.fitness_components, &c.fitness_components);
    (0.5 * sig * sig + 0.3 * op * op + 0.2 * fit * fit).sqrt()
}

fn op_distance(a: &[f32; 6], b: &[f32; 6]) -> f32 {
    let mut sum = 0.0f32;
    for i in 0..6 {
        let d = a[i] - b[i];
        sum += d * d;
    }
    let max = a
        .iter()
        .chain(b.iter())
        .copied()
        .fold(0.0f32, f32::max)
        .max(1.0);
    sum.sqrt() / (max * 6.0_f32.sqrt())
}

fn fitness_distance(a: &[f32; 4], b: &[f32; 4]) -> f32 {
    let mut sum = 0.0f32;
    for i in 0..4 {
        let d = a[i] - b[i];
        sum += d * d;
    }
    sum.sqrt() / 2.0
}

fn weighted_choice(weights: &[f32], sum: f32, rng: &mut StdRng) -> usize {
    let target: f32 = rng.random_range(0.0..sum);
    let mut acc = 0.0f32;
    for (i, w) in weights.iter().enumerate() {
        acc += w;
        if target < acc {
            return i;
        }
    }
    weights.len() - 1
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fake_individual(sig_byte: u8, fitness: f32) -> ClusterFeatures {
        ClusterFeatures {
            axiom_usage_signature: [sig_byte; MINHASH_SIG_LEN],
            op_skeleton: [0; 6],
            fitness_components: [fitness; 4],
        }
    }

    #[test]
    fn k_one_assigns_all_to_zero() {
        let pop: Vec<_> = (0..10).map(|i| fake_individual(i as u8, 0.0)).collect();
        let asg = cluster_individuals(&pop, 1, 42);
        assert!(asg.assignments.iter().all(|&c| c == 0));
        assert_eq!(asg.centroids.len(), 1);
    }

    #[test]
    fn well_separated_data_partitions_correctly() {
        let mut pop = Vec::new();
        for _ in 0..5 {
            pop.push(fake_individual(0x00, 0.0));
        }
        for _ in 0..5 {
            pop.push(fake_individual(0xFF, 1.0));
        }
        let asg = cluster_individuals(&pop, 2, 42);
        let label_a = asg.assignments[0];
        let label_b = asg.assignments[5];
        assert_ne!(label_a, label_b);
        assert!(asg.assignments[..5].iter().all(|&c| c == label_a));
        assert!(asg.assignments[5..].iter().all(|&c| c == label_b));
    }

    #[test]
    fn deterministic_for_same_seed() {
        let pop: Vec<_> = (0..20)
            .map(|i| fake_individual(i as u8, i as f32 / 20.0))
            .collect();
        let a = cluster_individuals(&pop, 4, 7);
        let b = cluster_individuals(&pop, 4, 7);
        assert_eq!(a.assignments, b.assignments);
    }

    #[test]
    fn empty_population_returns_sentinel() {
        let asg = cluster_individuals(&[], 4, 0);
        assert!(asg.assignments.is_empty());
        assert_eq!(asg.centroids.len(), 1);
    }

    #[test]
    fn k_clamped_to_population_size() {
        let pop: Vec<_> = (0..3).map(|i| fake_individual(i as u8, 0.0)).collect();
        let asg = cluster_individuals(&pop, 100, 0);
        assert!(asg.centroids.len() <= 3);
    }
}
