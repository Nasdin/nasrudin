//! Target-shape and sub-goal-ladder fitness signals.
//!
//! Pure-random GA over a thousand-axiom store has effectively zero
//! probability of composing the canonical 6-step chain to E=mc². The
//! search needs *direction*: a fitness signal that scores chains by how
//! structurally close their final `Expr` is to the headline target,
//! plus partial credit for reaching intermediate rungs of a known
//! decomposition.
//!
//! This module is the *only* place targets are mentioned in the GA. The
//! AxiomStore never sees the target or the ladder rungs — they're
//! fitness metadata, not building blocks. The no-cheat audit verifies
//! that none of the registered axioms canonical-form-equal any
//! configured target/rung.
//!
//! ## Target spec
//!
//! A `TargetSpec` has:
//! - `name`           — short identifier (e.g. "sr_rest_energy")
//! - `final_target`   — the headline canonical statement we want to
//!                      rediscover, as an `Expr` tree
//! - `ladder`         — ordered intermediate `Expr` shapes a complete
//!                      derivation must pass through (or close to). The
//!                      i-th rung is *strictly* more structurally
//!                      similar to the final target than the i-1th.
//!
//! Currently shipped specs:
//! - **`sr_rest_energy`** — Special Relativity rest-energy E = m·c².
//!   Ladder: `pᵘp_µ = m²c²` → `E² = (mc²)² + (pc)²` → `E² = (mc²)²` →
//!   `E = m·c²`.
//!
//! ## Scoring
//!
//! [`shape_similarity`] returns a value in `[0, 1]`:
//! - `1.0` when the candidate's canonical form bit-matches the target.
//! - High values for shapes that share root operator, structural
//!   topology, and the target's symbol set (`E`, `m`, `c`).
//! - Low values for the reflexive tautology `(m·c)² = (m·c)²` even
//!   though it contains the same symbols — the topology is wrong (it's
//!   `Eq(X, X)` rather than `Eq(leaf, expression)`).
//!
//! [`ladder_score`] returns the maximum [`shape_similarity`] across
//! all rungs of the ladder, weighted so reaching a higher rung scores
//! strictly more than reaching a lower one. This gives the GA gradient
//! information: a chain that produces the rung-2 shape outscores a
//! chain that produces the rung-1 shape, even if both are equally
//! "close" by raw similarity to the final target.

use nasrudin_core::{BinOp, Expr, PhysConst};
use std::collections::HashSet;

/// A symbolic target the GA should rediscover.
#[derive(Debug, Clone)]
pub struct TargetSpec {
    pub name: &'static str,
    pub final_target: Expr,
    /// Ordered intermediate shapes the canonical derivation passes
    /// through; rung[0] is the earliest, rung[N-1] is closest to
    /// (or equal to) `final_target`.
    pub ladder: Vec<Expr>,
}

impl TargetSpec {
    /// Look up a built-in spec by name.
    pub fn lookup(name: &str) -> Option<TargetSpec> {
        match name {
            "sr_rest_energy" => Some(sr_rest_energy()),
            _ => None,
        }
    }
}

/// SR rest-energy target: `E = m * c^2`.
///
/// Ladder rungs (in canonical-form order):
///
/// 1. `E² = (m·c²)² + (p·c)²` — full energy-momentum relation.
/// 2. `E² = (m·c²)²`          — at rest (p = 0 substituted).
/// 3. `E = m·c²`              — final, after positive square root.
///
/// (We omit the `pᵘp_µ = m²c²` invariant-mass step from the ladder
/// because it's a different syntactic shape — it lives in the
/// 4-vector world, not the scalar (E, m, c, p) world the chain
/// actually navigates.)
pub fn sr_rest_energy() -> TargetSpec {
    let e = || Expr::Var("E".into());
    let m = || Expr::Var("m".into());
    let p = || Expr::Var("p".into());
    let c = || Expr::Const(PhysConst::SpeedOfLight);
    let two = || Expr::Lit(2, 1);
    let pow = |a: Expr, b: Expr| Expr::BinOp(BinOp::Pow, Box::new(a), Box::new(b));
    let mul = |a: Expr, b: Expr| Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(b));
    let add = |a: Expr, b: Expr| Expr::BinOp(BinOp::Add, Box::new(a), Box::new(b));
    let eq = |a: Expr, b: Expr| Expr::BinOp(BinOp::Eq, Box::new(a), Box::new(b));

    let mc2 = mul(m(), pow(c(), two()));
    let pc = mul(p(), c());
    let e_sq = pow(e(), two());
    let mc2_sq = pow(mc2.clone(), two());
    let pc_sq = pow(pc, two());

    // Rung 1: E² = (m·c²)² + (p·c)²
    let rung1 = eq(e_sq.clone(), add(mc2_sq.clone(), pc_sq));
    // Rung 2: E² = (m·c²)² (p=0)
    let rung2 = eq(e_sq, mc2_sq);
    // Rung 3 / final target: E = m·c²
    let final_target = eq(e(), mc2);

    TargetSpec {
        name: "sr_rest_energy",
        ladder: vec![rung1, rung2, final_target.clone()],
        final_target,
    }
}

/// Score how closely `candidate` matches `target`, in `[0, 1]`.
///
/// Three components, equally weighted:
/// - **Symbol overlap** — how many of the target's distinct symbols
///   (`Var`, `Const`, `Lit`) appear in the candidate.
/// - **Root-operator match** — whether the top-level operator agrees.
///   For an `Eq`-rooted target, an `Eq`-rooted candidate gets full
///   marks here; anything else gets 0. This is what filters out
///   non-equation candidates and the all-too-tempting `Eq(X, X)`
///   tautology pattern (we deduct half if `lhs == rhs`).
/// - **Topological similarity** — recursive node-count ratio between
///   corresponding subtrees. Diverging branches drop the score.
pub fn shape_similarity(candidate: &Expr, target: &Expr) -> f64 {
    let cand_canon = candidate.to_canonical();
    let target_canon = target.to_canonical();
    if cand_canon == target_canon {
        return 1.0;
    }

    // Reflexive equation `Eq(X, X)` is the failure mode the GA collapses
    // onto under naive fitness — same symbols as the target, root-op
    // matches, but trivially true. Hard-cap at 0.1 so any non-trivial
    // structurally-close candidate dominates.
    if let Expr::BinOp(BinOp::Eq, l, r) = candidate
        && l.to_canonical() == r.to_canonical()
    {
        return 0.1;
    }

    let sym_score = symbol_overlap(candidate, target);
    let root_score = root_operator_score(candidate, target);
    let topo_score = topology_score(candidate, target);

    // Symbol overlap gates the rest: a candidate whose symbols are
    // disjoint from the target gets near-zero regardless of topology
    // or root match. (`a = b` shouldn't get half-credit toward `E=mc²`
    // just because it's an equation.) The √ taper keeps gentle gradient
    // for partial overlaps.
    let sym_gate = sym_score.sqrt();
    (sym_score + root_score * sym_gate + topo_score * sym_gate) / 3.0
}

/// Return the maximum ladder score for a candidate against a spec.
///
/// Each rung is weighted by `(i+1)/N` so reaching rung 2 of 3 outscores
/// reaching rung 1 even if the raw similarity is the same.
pub fn ladder_score(candidate: &Expr, spec: &TargetSpec) -> f64 {
    if spec.ladder.is_empty() {
        return shape_similarity(candidate, &spec.final_target);
    }
    let n = spec.ladder.len() as f64;
    spec.ladder
        .iter()
        .enumerate()
        .map(|(i, rung)| {
            let weight = ((i + 1) as f64) / n;
            shape_similarity(candidate, rung) * weight
        })
        .fold(0.0_f64, f64::max)
}

/// Score a chain's *prefix* by how well its accumulated facts cover
/// the symbols in the target shape, in `[0, 1]`.
///
/// The motivating failure mode: a chain
/// `[IntroduceAxiom("kinetic_energy_def"), RearrangeEquation(target=E=mc²)]`
/// has `shape_similarity(final, target) = 1.0` (RearrangeEquation just
/// claims its target as the new `current`), but the only fact in scope
/// is `KE = ½mv²` — Lean's nlinarith has no chance of discharging
/// `E = m·c²` from that. We need a fitness component that grades the
/// *path*, not just the leaf.
///
/// Coverage = |target_symbols ∩ ⋃ intro-axiom symbols| / |target_symbols|.
/// Higher = more target symbols are bound by the accumulated hypotheses.
pub fn chain_coverage(
    chain: &[nasrudin_derive::RuleStep],
    store: &nasrudin_derive::AxiomStore,
    target: &TargetSpec,
) -> f64 {
    let target_syms = collect_symbols(&target.final_target);
    if target_syms.is_empty() {
        return 1.0;
    }
    let mut prefix_syms = HashSet::new();
    for step in chain {
        let name = match step {
            nasrudin_derive::RuleStep::IntroduceAxiom { axiom_name } => axiom_name,
            nasrudin_derive::RuleStep::IntroduceTheorem { theorem_name } => theorem_name,
            _ => continue,
        };
        if let Some(ax) = store.get(name) {
            collect_symbols_into(&ax.statement, &mut prefix_syms);
        }
    }
    let hit = target_syms.iter().filter(|s| prefix_syms.contains(*s)).count();
    hit as f64 / target_syms.len() as f64
}

// ---- internals -------------------------------------------------------------

fn symbol_overlap(candidate: &Expr, target: &Expr) -> f64 {
    let target_syms = collect_symbols(target);
    if target_syms.is_empty() {
        return 1.0;
    }
    let cand_syms = collect_symbols(candidate);
    let hit: usize = target_syms
        .iter()
        .filter(|s| cand_syms.contains(*s))
        .count();
    hit as f64 / target_syms.len() as f64
}

fn root_operator_score(candidate: &Expr, target: &Expr) -> f64 {
    match (candidate, target) {
        (Expr::BinOp(co, cl, cr), Expr::BinOp(to, _, _)) if co == to => {
            // Root op matches. Penalise the reflexive tautology
            // `Eq(X, X)` — same canonical on both sides — heavily; that's
            // the failure mode the current run hit.
            if co == &BinOp::Eq && cl.to_canonical() == cr.to_canonical() {
                0.25
            } else {
                1.0
            }
        }
        (Expr::BinOp(_, _, _), Expr::BinOp(_, _, _)) => 0.4,
        _ => 0.0,
    }
}

fn topology_score(candidate: &Expr, target: &Expr) -> f64 {
    let cn = node_count(candidate) as f64;
    let tn = node_count(target) as f64;
    if cn == 0.0 || tn == 0.0 {
        return 0.0;
    }
    let ratio = cn.min(tn) / cn.max(tn);

    // Recurse into matching subtrees of binary ops.
    if let (Expr::BinOp(co, cl, cr), Expr::BinOp(to, tl, tr)) = (candidate, target)
        && co == to
    {
        let l = topology_score(cl, tl);
        let r = topology_score(cr, tr);
        return (ratio + (l + r) / 2.0) / 2.0;
    }
    ratio
}

fn collect_symbols(expr: &Expr) -> HashSet<String> {
    let mut out = HashSet::new();
    collect_symbols_into(expr, &mut out);
    out
}

fn collect_symbols_into(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        Expr::Var(name) => {
            out.insert(format!("var:{name}"));
        }
        Expr::Const(c) => {
            out.insert(format!("const:{c:?}"));
        }
        Expr::Lit(num, den) => {
            out.insert(format!("lit:{num}/{den}"));
        }
        Expr::BinOp(_, l, r) => {
            collect_symbols_into(l, out);
            collect_symbols_into(r, out);
        }
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => {
            collect_symbols_into(e, out);
        }
        Expr::App(f, x) => {
            collect_symbols_into(f, out);
            collect_symbols_into(x, out);
        }
        _ => {}
    }
}

fn node_count(expr: &Expr) -> usize {
    match expr {
        Expr::BinOp(_, l, r) => 1 + node_count(l) + node_count(r),
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => 1 + node_count(e),
        Expr::App(f, x) => 1 + node_count(f) + node_count(x),
        _ => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e_var() -> Expr {
        Expr::Var("E".into())
    }
    fn m_var() -> Expr {
        Expr::Var("m".into())
    }
    fn c_const() -> Expr {
        Expr::Const(PhysConst::SpeedOfLight)
    }
    fn lit2() -> Expr {
        Expr::Lit(2, 1)
    }
    fn pow(a: Expr, b: Expr) -> Expr {
        Expr::BinOp(BinOp::Pow, Box::new(a), Box::new(b))
    }
    fn mul(a: Expr, b: Expr) -> Expr {
        Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(b))
    }
    fn eq(a: Expr, b: Expr) -> Expr {
        Expr::BinOp(BinOp::Eq, Box::new(a), Box::new(b))
    }

    #[test]
    fn exact_match_scores_one() {
        let target = sr_rest_energy().final_target;
        assert_eq!(shape_similarity(&target, &target), 1.0);
    }

    #[test]
    fn reflexive_tautology_scores_low() {
        // `(m*c)² = (m*c)²` — the failure mode we just hit.
        let mc = mul(m_var(), c_const());
        let lhs = pow(mc.clone(), lit2());
        let rhs = pow(mc, lit2());
        let tautology = eq(lhs, rhs);
        let target = sr_rest_energy().final_target;
        let score = shape_similarity(&tautology, &target);
        assert!(
            score < 0.5,
            "reflexive Eq(X,X) should score < 0.5, got {score}"
        );
    }

    #[test]
    fn rung_climbs_increase_score() {
        let spec = sr_rest_energy();
        // The ladder is: E²=(mc²)²+(pc)² → E²=(mc²)² → E=mc²
        let s0 = ladder_score(&spec.ladder[0], &spec);
        let s1 = ladder_score(&spec.ladder[1], &spec);
        let s2 = ladder_score(&spec.ladder[2], &spec);
        assert!(s0 < s1, "rung 1 ({s0}) < rung 2 ({s1}) failed");
        assert!(s1 < s2, "rung 2 ({s1}) < rung 3 ({s2}) failed");
        assert!((s2 - 1.0).abs() < 1e-9, "final rung should ≈ 1, got {s2}");
    }

    #[test]
    fn unrelated_expr_scores_low() {
        let target = sr_rest_energy().final_target;
        let unrelated = eq(Expr::Var("a".into()), Expr::Var("b".into()));
        let score = shape_similarity(&unrelated, &target);
        assert!(
            score < 0.4,
            "completely unrelated expr should score low, got {score}"
        );
    }

    #[test]
    fn close_match_scores_high() {
        // E² = (mc²)² — rung 2, structurally close to E=mc².
        let target = sr_rest_energy().final_target;
        let mc2 = mul(m_var(), pow(c_const(), lit2()));
        let close = eq(pow(e_var(), lit2()), pow(mc2, lit2()));
        let score = shape_similarity(&close, &target);
        assert!(
            score > 0.5,
            "structurally close shape should score > 0.5, got {score}"
        );
    }

    #[test]
    fn forbidden_target_audit_helper() {
        // Doc test: lookup must succeed for known specs and fail for
        // anything else.
        assert!(TargetSpec::lookup("sr_rest_energy").is_some());
        assert!(TargetSpec::lookup("does_not_exist").is_none());
    }
}
