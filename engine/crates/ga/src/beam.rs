//! Beam search over derivation states.
//!
//! Pure-random GA over a thousand-axiom store has effectively zero
//! probability of composing the canonical 6-step chain to E=mc². Beam
//! search is the goal-directed alternative: maintain a small frontier
//! of best-scoring chains, expand each by one rule application per
//! step, and prune by ladder distance to the target. We're trading
//! breadth for depth — fewer chains explored, but each one informed by
//! how close it is to the target shape.
//!
//! The two algorithms are complementary, not exclusive: the GA worker
//! explores broadly, the beam worker exploits direction. Both submit
//! verified discoveries to `/api/ingest`; the chain firewall doesn't
//! care which producer found the proof.
//!
//! ## Algorithm
//!
//! State = `(chain, current_expr, score)`. Score is `ladder_score` from
//! `target.rs` so the beam climbs the sub-goal ladder.
//!
//! Each iteration:
//! 1. Take the top-`beam_width` states by score.
//! 2. For each, try every legal next-step expansion:
//!    - `IntroduceAxiom(name)` for every axiom in the store
//!    - `AlgebraicSimplify`
//!    - `TakePositiveRoot` (when `current_expr` is `Eq(Pow(_,2), Pow(_,2))`)
//!    - skip `RearrangeEquation` and `SubstituteValue` for now —
//!      they have continuous parameters and explode the branching.
//! 3. Score each expansion's resulting Expr.
//! 4. Replace the frontier with the top-`beam_width` of the new states.
//! 5. Stop when any state's `target_shape` ≥ `accept_threshold`, when
//!    we exceed `max_depth`, or when the frontier stagnates.

use std::cmp::Ordering;

use nasrudin_core::{BinOp, Expr};
use nasrudin_derive::{
    AxiomStore, Chain, DerivationContext, RuleStep, strategies::DerivationStrategy,
};

use crate::target::{ladder_score, shape_similarity, TargetSpec};

/// Configuration for [`beam_search`].
#[derive(Debug, Clone)]
pub struct BeamConfig {
    /// Number of states retained in the frontier per iteration.
    pub beam_width: usize,
    /// Maximum chain depth before giving up.
    pub max_depth: usize,
    /// `target_shape` threshold above which a state is reported as a
    /// candidate match (the caller is expected to lake-verify it).
    pub accept_threshold: f64,
    /// If the best-frontier score doesn't improve for this many
    /// iterations, terminate early.
    pub stagnation_window: usize,
}

impl Default for BeamConfig {
    fn default() -> Self {
        Self {
            beam_width: 32,
            max_depth: 12,
            accept_threshold: 0.95,
            stagnation_window: 5,
        }
    }
}

/// One item on the beam: a chain executed against the AxiomStore that
/// produced `expr`, plus its ladder score.
#[derive(Debug, Clone)]
pub struct BeamState {
    pub chain: Chain,
    pub expr: Expr,
    pub ladder: f64,
    pub shape: f64,
}

impl BeamState {
    fn score(&self) -> f64 {
        // Composite: ladder (partial credit) dominates, shape (final
        // target) breaks ties when two states are on the same rung.
        self.ladder + 0.1 * self.shape
    }
}

/// Result of a beam-search run.
#[derive(Debug, Clone)]
pub struct BeamReport {
    pub iterations: usize,
    pub frontier_final: Vec<BeamState>,
    /// States whose `target_shape` cleared `accept_threshold`. Caller
    /// should run `verify_chain` on these.
    pub candidates: Vec<BeamState>,
}

/// Run beam search starting from each axiom in `store` (1-step seeds).
/// Returns the accumulated report.
pub fn beam_search(store: &AxiomStore, target: &TargetSpec, cfg: &BeamConfig) -> BeamReport {
    // Seed: every axiom becomes a 1-step chain.
    let mut frontier: Vec<BeamState> = store
        .iter()
        .filter_map(|ax| {
            let chain = Chain(vec![RuleStep::IntroduceAxiom {
                axiom_name: ax.name.clone(),
            }]);
            let expr = run_chain(&chain, store)?;
            let shape = shape_similarity(&expr, &target.final_target);
            let ladder = ladder_score(&expr, target);
            Some(BeamState { chain, expr, ladder, shape })
        })
        .collect();

    sort_and_truncate(&mut frontier, cfg.beam_width);

    let mut candidates: Vec<BeamState> = Vec::new();
    let mut iterations = 0;
    let mut last_best = frontier.first().map(|s| s.score()).unwrap_or(0.0);
    let mut stagnant_for = 0;

    for depth in 1..cfg.max_depth {
        iterations = depth;
        let mut next: Vec<BeamState> = Vec::new();

        for state in &frontier {
            // Enumerate next-step expansions.
            //
            // 1. Every IntroduceAxiom in the store.
            for ax in store.iter() {
                let mut next_chain = state.chain.clone();
                next_chain.push(RuleStep::IntroduceAxiom {
                    axiom_name: ax.name.clone(),
                });
                if let Some(expr) = run_chain(&next_chain, store) {
                    let shape = shape_similarity(&expr, &target.final_target);
                    let ladder = ladder_score(&expr, target);
                    next.push(BeamState { chain: next_chain, expr, ladder, shape });
                }
            }
            // 2. AlgebraicSimplify (parameter-free).
            let mut next_chain = state.chain.clone();
            next_chain.push(RuleStep::AlgebraicSimplify);
            if let Some(expr) = run_chain(&next_chain, store) {
                let shape = shape_similarity(&expr, &target.final_target);
                let ladder = ladder_score(&expr, target);
                next.push(BeamState { chain: next_chain, expr, ladder, shape });
            }
            // 3. TakePositiveRoot when applicable: only meaningful when
            //    `current_expr` is `Eq(Pow(_,2), Pow(_,2))`.
            if matches!(
                &state.expr,
                Expr::BinOp(BinOp::Eq, l, r)
                    if matches!(l.as_ref(), Expr::BinOp(BinOp::Pow, _, _))
                        && matches!(r.as_ref(), Expr::BinOp(BinOp::Pow, _, _))
            ) {
                let mut next_chain = state.chain.clone();
                next_chain.push(RuleStep::TakePositiveRoot);
                if let Some(expr) = run_chain(&next_chain, store) {
                    let shape = shape_similarity(&expr, &target.final_target);
                    let ladder = ladder_score(&expr, target);
                    next.push(BeamState { chain: next_chain, expr, ladder, shape });
                }
            }
        }

        // Capture candidates that cleared the threshold this iteration.
        for state in &next {
            if state.shape >= cfg.accept_threshold {
                candidates.push(state.clone());
            }
        }

        // Dedup by canonical form to stop the beam from wallowing in
        // the same expression with different chain prefixes.
        sort_and_truncate(&mut next, cfg.beam_width * 4);
        dedup_by_canonical(&mut next);
        sort_and_truncate(&mut next, cfg.beam_width);

        let new_best = next.first().map(|s| s.score()).unwrap_or(0.0);
        if new_best <= last_best + 1e-6 {
            stagnant_for += 1;
            if stagnant_for >= cfg.stagnation_window {
                frontier = next;
                break;
            }
        } else {
            stagnant_for = 0;
            last_best = new_best;
        }
        frontier = next;

        // Early stop on perfect match.
        if frontier.first().map(|s| s.shape).unwrap_or(0.0) >= 0.999 {
            break;
        }
    }

    BeamReport {
        iterations,
        frontier_final: frontier,
        candidates,
    }
}

fn run_chain(chain: &Chain, store: &AxiomStore) -> Option<Expr> {
    let mut ctx = DerivationContext::new();
    chain.execute(store, &mut ctx).ok()
}

fn sort_and_truncate(states: &mut Vec<BeamState>, width: usize) {
    states.sort_by(|a, b| {
        b.score()
            .partial_cmp(&a.score())
            .unwrap_or(Ordering::Equal)
    });
    if states.len() > width {
        states.truncate(width);
    }
}

fn dedup_by_canonical(states: &mut Vec<BeamState>) {
    let mut seen = std::collections::HashSet::new();
    states.retain(|s| {
        let canon = s.expr.to_canonical();
        seen.insert(canon)
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    fn upstream_sr_store() -> AxiomStore {
        let mut s = AxiomStore::new();
        s.load_special_relativity_upstream();
        s
    }

    #[test]
    fn beam_seeds_from_axioms() {
        let store = upstream_sr_store();
        let target = crate::target::sr_rest_energy();
        let cfg = BeamConfig {
            beam_width: 8,
            max_depth: 1, // just confirm seeding works
            accept_threshold: 1.0,
            stagnation_window: 1,
        };
        let report = beam_search(&store, &target, &cfg);
        assert!(!report.frontier_final.is_empty());
        // Each seed should have a 1-step chain.
        for s in &report.frontier_final {
            assert_eq!(s.chain.0.len(), 1);
        }
    }

    #[test]
    fn beam_prefers_higher_ladder_states() {
        let store = upstream_sr_store();
        let target = crate::target::sr_rest_energy();
        let cfg = BeamConfig {
            beam_width: 8,
            max_depth: 4,
            accept_threshold: 1.0,
            stagnation_window: 4,
        };
        let report = beam_search(&store, &target, &cfg);
        // Frontier should be sorted by score descending.
        for w in report.frontier_final.windows(2) {
            assert!(w[0].score() >= w[1].score());
        }
    }
}
