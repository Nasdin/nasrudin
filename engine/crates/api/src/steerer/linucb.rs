//! Pure-CPU LinUCB contextual bandit for the per-cluster directive
//! multipliers.
//!
//! For each (island_domain, action) slot, maintain ridge-regression
//! sufficient statistics A (6×6) and b (6×1) over the feature vector
//!
//!   x(s, c) = [1, s, s², c, c², s·c]
//!
//! where `s` ∈ [0, 1] is the LLM-emitted strength and `c` ∈ [0, 1] is
//! the multiplier_choice normalised by `MAX_MULTIPLIER_CHOICES - 1`.
//! Rank-1 online update on each pull:
//!
//!   A ← A + x xᵀ,   b ← b + r·x
//!
//! Selection: θ = A⁻¹ b. For each candidate (s_now, c), predict
//!
//!   ŷ(c) = θᵀ x(s_now, c)
//!   σ²(c) = x(s_now, c)ᵀ A⁻¹ x(s_now, c)
//!
//! Pick argmax_c (ŷ(c) + α·√σ²(c)). Classic LinUCB with explicit
//! exploration term; α=1.0 is a moderate default.
//!
//! Hand-coded 6×6 ops avoid pulling in a linear-algebra dep. d=6 is
//! small enough that matrix inversion is ~200 flops — microseconds
//! on any CPU. No GPU, no FFI, no Python, no offline training.

pub const FEATURE_DIM: usize = 6;
const D: usize = FEATURE_DIM;

/// Ridge regularisation. Chosen so the prior on θ is mildly
/// informative: as `pulls → 0`, predictions decay toward 0 cleanly
/// instead of diverging.
pub const LINUCB_LAMBDA: f64 = 1.0;

/// LinUCB exploration coefficient. 1.0 = moderate; higher = more
/// exploration of high-uncertainty candidates.
pub const LINUCB_ALPHA: f64 = 1.0;

/// Pull threshold below which the worker should fall back to the
/// discrete UCB1 path. LinUCB's predictions are unreliable until the
/// sufficient statistics reflect a few real pulls; UCB1's
/// cold-start handles the early phase better.
pub const LINUCB_WARMUP_PULLS: i64 = 30;

/// Compute the LinUCB feature vector for (strength, choice).
/// `choice` is normalised by dividing by `max_choice` (typically
/// `MAX_MULTIPLIER_CHOICES - 1 = 8`) so both axes share a [0, 1]
/// range — keeps the conditioning of A clean.
pub fn features(strength: f64, choice: u8, max_choice: u8) -> [f64; D] {
    let s = strength.clamp(0.0, 1.0);
    let denom = max_choice.max(1) as f64;
    let c = (choice as f64 / denom).clamp(0.0, 1.0);
    [1.0, s, s * s, c, c * c, s * c]
}

/// Initialise A = λ·I as a flat 36-element row-major vector.
pub fn init_a_flat(lambda: f64) -> Vec<f64> {
    let mut a = vec![0.0; D * D];
    for i in 0..D {
        a[i * D + i] = lambda;
    }
    a
}

/// Online rank-1 update: A ← A + x·xᵀ, b ← b + r·x. Operates in
/// place on the flat (row-major) storage that PG round-trips
/// without any matrix conversion.
pub fn update_in_place(a_flat: &mut [f64], b: &mut [f64], x: &[f64; D], reward: f64) {
    debug_assert_eq!(a_flat.len(), D * D);
    debug_assert_eq!(b.len(), D);
    for i in 0..D {
        b[i] += reward * x[i];
        for j in 0..D {
            a_flat[i * D + j] += x[i] * x[j];
        }
    }
}

/// Solve `A·θ = b` for θ via Gauss-Jordan elimination with partial
/// pivoting. Pure 6×6 hand-coded; ~120 flops. Returns `None` only
/// if A is singular (impossible in practice with λ > 0).
pub fn solve_a_b(a_flat: &[f64], b: &[f64]) -> Option<[f64; D]> {
    debug_assert_eq!(a_flat.len(), D * D);
    debug_assert_eq!(b.len(), D);
    // Augmented matrix [A | b]
    let mut m = [[0.0f64; D + 1]; D];
    for i in 0..D {
        for j in 0..D {
            m[i][j] = a_flat[i * D + j];
        }
        m[i][D] = b[i];
    }
    for k in 0..D {
        // Partial pivoting.
        let mut pivot = k;
        let mut pivot_abs = m[k][k].abs();
        for i in k + 1..D {
            let v = m[i][k].abs();
            if v > pivot_abs {
                pivot_abs = v;
                pivot = i;
            }
        }
        if pivot_abs < 1e-12 {
            return None; // singular
        }
        if pivot != k {
            m.swap(k, pivot);
        }
        // Normalise pivot row.
        let pv = m[k][k];
        for j in k..=D {
            m[k][j] /= pv;
        }
        // Eliminate other rows.
        for i in 0..D {
            if i == k {
                continue;
            }
            let f = m[i][k];
            if f == 0.0 {
                continue;
            }
            for j in k..=D {
                m[i][j] -= f * m[k][j];
            }
        }
    }
    let mut theta = [0.0f64; D];
    for i in 0..D {
        theta[i] = m[i][D];
    }
    Some(theta)
}

/// Compute `xᵀ A⁻¹ x` for the LinUCB exploration term. Solves
/// `A·v = x`, then returns `xᵀv`. Same Gauss-Jordan as `solve_a_b`
/// but with x in place of b.
pub fn solve_quadratic_form(a_flat: &[f64], x: &[f64; D]) -> Option<f64> {
    let v = solve_a_b(a_flat, x)?;
    let mut q = 0.0f64;
    for i in 0..D {
        q += x[i] * v[i];
    }
    Some(q)
}

/// LinUCB score for a candidate (strength, choice): predicted
/// reward + α · sqrt(uncertainty). Returns None when A is singular
/// (caller should fall through to UCB1).
pub fn score(a_flat: &[f64], b: &[f64], strength: f64, choice: u8, max_choice: u8) -> Option<f64> {
    let x = features(strength, choice, max_choice);
    let theta = solve_a_b(a_flat, b)?;
    let mut mean = 0.0f64;
    for i in 0..D {
        mean += theta[i] * x[i];
    }
    let var = solve_quadratic_form(a_flat, &x)?;
    let sigma = var.max(0.0).sqrt();
    Some(mean + LINUCB_ALPHA * sigma)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn features_normalises_choice() {
        let x = features(0.5, 4, 8);
        assert_eq!(x[0], 1.0);
        assert!((x[1] - 0.5).abs() < 1e-12);
        assert!((x[2] - 0.25).abs() < 1e-12);
        assert!((x[3] - 0.5).abs() < 1e-12);
        assert!((x[4] - 0.25).abs() < 1e-12);
        assert!((x[5] - 0.25).abs() < 1e-12);
    }

    #[test]
    fn features_clamp_out_of_range() {
        let x = features(1.5, 99, 8);
        assert!((x[1] - 1.0).abs() < 1e-12);
        assert!((x[3] - 1.0).abs() < 1e-12);
    }

    #[test]
    fn init_a_is_lambda_identity() {
        let a = init_a_flat(2.0);
        for i in 0..D {
            for j in 0..D {
                let expected = if i == j { 2.0 } else { 0.0 };
                assert!((a[i * D + j] - expected).abs() < 1e-12);
            }
        }
    }

    #[test]
    fn solve_recovers_theta_for_identity() {
        // A = I, b = [1,2,3,4,5,6] → θ = b
        let mut a = init_a_flat(1.0);
        let b: Vec<f64> = (1..=D).map(|i| i as f64).collect();
        let theta = solve_a_b(&a, &b).unwrap();
        for i in 0..D {
            assert!((theta[i] - (i as f64 + 1.0)).abs() < 1e-9);
        }
        let _ = &mut a;
    }

    #[test]
    fn rank_1_update_increments_diagonal() {
        let mut a = init_a_flat(1.0);
        let mut b = vec![0.0; D];
        let x = features(0.5, 4, 8);
        update_in_place(&mut a, &mut b, &x, 0.7);
        // Off-diagonal entries became non-zero (e.g. x[0]·x[1] = 0.5)
        assert!((a[0 * D + 1] - 0.5).abs() < 1e-12);
        // Diagonal entry [0][0] = λ + x[0]² = 1 + 1 = 2.
        assert!((a[0 * D + 0] - 2.0).abs() < 1e-12);
        // b updated by reward·x.
        assert!((b[0] - 0.7).abs() < 1e-12);
        assert!((b[1] - 0.35).abs() < 1e-12);
    }

    #[test]
    fn score_runs_and_is_finite_after_update() {
        let mut a = init_a_flat(1.0);
        let mut b = vec![0.0; D];
        for _ in 0..10 {
            let x = features(0.5, 4, 8);
            update_in_place(&mut a, &mut b, &x, 0.8);
        }
        let s = score(&a, &b, 0.5, 4, 8).unwrap();
        assert!(s.is_finite());
        // After many positive-reward pulls at this point, score > 0.
        assert!(s > 0.0);
    }

    #[test]
    fn score_uncertainty_decreases_with_pulls() {
        // After many pulls at (s, c), the LinUCB exploration bonus
        // for that exact point should shrink.
        let mut a = init_a_flat(1.0);
        let mut b = vec![0.0; D];
        let x = features(0.5, 4, 8);
        let s_before = score(&a, &b, 0.5, 4, 8).unwrap();
        for _ in 0..100 {
            update_in_place(&mut a, &mut b, &x, 0.5);
        }
        let s_after = score(&a, &b, 0.5, 4, 8).unwrap();
        // The uncertainty bonus shrinks, so the score should be
        // closer to the mean (0.5) and less than the cold-start
        // bonus-driven score.
        assert!(
            s_after < s_before,
            "expected LinUCB score to decrease as uncertainty shrinks; \
             before={s_before} after={s_after}"
        );
    }
}
