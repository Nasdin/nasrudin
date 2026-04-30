//! Per-individual feature vector for k-means clustering.
//!
//! Components:
//! - `axiom_usage_signature`: 16-byte min-hash over axiom / theorem
//!   names referenced by the chain. Hamming distance over the
//!   signature approximates 1 - Jaccard similarity over the underlying
//!   name set, so two chains drawing from the same axioms have a low
//!   distance regardless of the order they reference them.
//! - `op_skeleton`: count per RuleStep variant.
//! - `fitness_components`: normalised fitness sub-scores (novelty,
//!   dimensional elegance, length penalty, target proximity).

use nasrudin_derive::{Chain, RuleStep};

pub const MINHASH_SIG_LEN: usize = 16;

#[derive(Debug, Clone, PartialEq)]
pub struct ClusterFeatures {
    pub axiom_usage_signature: [u8; MINHASH_SIG_LEN],
    pub op_skeleton: [u32; 6],
    pub fitness_components: [f32; 4],
}

impl ClusterFeatures {
    pub fn from_chain(chain: &Chain, fitness_components: &[f32; 4]) -> Self {
        let mut op_skeleton = [0u32; 6];
        let mut names: Vec<&str> = Vec::new();
        for step in chain.0.iter() {
            // Map each RuleStep variant to one of six operator buckets.
            // The ordering matches MUTATION_OPS in chain_ga so the
            // skeleton is interpretable alongside mutation_priors.
            let idx = match step {
                // 0 = insert_random  (no chain shape captures this — only
                //                     mutation history would; treat as 0)
                // 1 = delete_random  (same — mutation history)
                // 2 = swap_adjacent  (same)
                // 3 = mutate_axiom_name  → IntroduceAxiom / IntroduceTheorem
                RuleStep::IntroduceAxiom { .. } => 3,
                RuleStep::IntroduceTheorem { .. } => 3,
                // 4 = mutate_param  → SubstituteValue / AlgebraicSimplify
                RuleStep::SubstituteValue { .. } => 4,
                RuleStep::AlgebraicSimplify => 4,
                // 5 = append_productive_suffix  → RearrangeEquation /
                //                                 TakePositiveRoot
                RuleStep::RearrangeEquation { .. } => 5,
                RuleStep::TakePositiveRoot => 5,
            };
            op_skeleton[idx] = op_skeleton[idx].saturating_add(1);
            if let RuleStep::IntroduceAxiom { axiom_name } = step {
                names.push(axiom_name.as_str());
            }
            if let RuleStep::IntroduceTheorem { theorem_name } = step {
                names.push(theorem_name.as_str());
            }
        }
        let axiom_usage_signature = minhash_signature(&names);
        Self {
            axiom_usage_signature,
            op_skeleton,
            fitness_components: *fitness_components,
        }
    }
}

/// 16-byte min-hash. Each byte = min over names of (xxhash(name, seed_i) & 0xFF).
/// Empty input → all 0xFF (canonical empty signature).
fn minhash_signature(names: &[&str]) -> [u8; MINHASH_SIG_LEN] {
    let mut sig = [0xFFu8; MINHASH_SIG_LEN];
    if names.is_empty() {
        return sig;
    }
    for (i, slot) in sig.iter_mut().enumerate() {
        let seed = i as u64;
        let mut min_byte = 0xFFu8;
        for n in names {
            let h = xxhash_rust::xxh64::xxh64(n.as_bytes(), seed);
            let b = (h & 0xFF) as u8;
            if b < min_byte {
                min_byte = b;
            }
        }
        *slot = min_byte;
    }
    sig
}

/// Hamming distance between two min-hash signatures, normalised to [0, 1].
pub fn signature_distance(a: &[u8; MINHASH_SIG_LEN], b: &[u8; MINHASH_SIG_LEN]) -> f32 {
    let mut diff = 0u32;
    for i in 0..MINHASH_SIG_LEN {
        diff += (a[i] ^ b[i]).count_ones();
    }
    diff as f32 / (MINHASH_SIG_LEN as f32 * 8.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_core::Expr;

    #[test]
    fn empty_chain_yields_zero_op_skeleton() {
        let chain = Chain(vec![]);
        let f = ClusterFeatures::from_chain(&chain, &[0.1, 0.2, 0.3, 0.4]);
        assert_eq!(f.op_skeleton, [0; 6]);
        assert_eq!(f.fitness_components, [0.1, 0.2, 0.3, 0.4]);
        // Empty axiom set → canonical empty signature
        assert_eq!(f.axiom_usage_signature, [0xFFu8; MINHASH_SIG_LEN]);
    }

    #[test]
    fn identical_axiom_sets_have_identical_signatures() {
        let f1 = ClusterFeatures::from_chain(
            &Chain(vec![RuleStep::IntroduceAxiom {
                axiom_name: "lorentz_factor".into(),
            }]),
            &[0.0; 4],
        );
        let f2 = ClusterFeatures::from_chain(
            &Chain(vec![RuleStep::IntroduceAxiom {
                axiom_name: "lorentz_factor".into(),
            }]),
            &[0.0; 4],
        );
        assert_eq!(f1.axiom_usage_signature, f2.axiom_usage_signature);
    }

    #[test]
    fn different_axiom_sets_diverge() {
        let f1 = ClusterFeatures::from_chain(
            &Chain(vec![RuleStep::IntroduceAxiom {
                axiom_name: "lorentz_factor".into(),
            }]),
            &[0.0; 4],
        );
        let f2 = ClusterFeatures::from_chain(
            &Chain(vec![RuleStep::IntroduceAxiom {
                axiom_name: "planck_constant".into(),
            }]),
            &[0.0; 4],
        );
        let d = signature_distance(&f1.axiom_usage_signature, &f2.axiom_usage_signature);
        assert!(d > 0.05, "expected meaningful divergence, got {d}");
    }

    #[test]
    fn op_skeleton_counts_each_variant() {
        let chain = Chain(vec![
            RuleStep::IntroduceAxiom {
                axiom_name: "a".into(),
            },
            RuleStep::IntroduceAxiom {
                axiom_name: "b".into(),
            },
            RuleStep::SubstituteValue {
                var: "x".into(),
                value: Expr::Var("y".into()),
                reason: "".into(),
            },
            RuleStep::AlgebraicSimplify,
            RuleStep::TakePositiveRoot,
        ]);
        let f = ClusterFeatures::from_chain(&chain, &[0.0; 4]);
        // Bucket 3: 2 IntroduceAxiom; bucket 4: SubstituteValue + AlgebraicSimplify
        // bucket 5: TakePositiveRoot
        assert_eq!(f.op_skeleton[3], 2);
        assert_eq!(f.op_skeleton[4], 2);
        assert_eq!(f.op_skeleton[5], 1);
    }
}
