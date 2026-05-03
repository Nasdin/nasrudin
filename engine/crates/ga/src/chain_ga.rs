//! Chain-based GA: mutation + crossover over `Chain<RuleStep>`.
//!
//! Phase 5 of the project plan. The GA evolves `Chain`s — sequences of
//! generic `RuleStep`s — instead of raw `Expr` ASTs. The pre-filter
//! is `Chain::execute`: any chain that fails to apply (axiom missing,
//! rule preconditions not met, etc.) is rejected before reaching the
//! Lean verifier.
//!
//! ## Mutation operators
//!
//! - `Insert`        — insert a random valid `RuleStep` at a random position.
//! - `Delete`        — remove a random step (with at-least-one bound).
//! - `Swap`          — swap two adjacent steps.
//! - `MutateAxiom`   — change the axiom name of an `IntroduceAxiom` step
//!                     to a different one in the store.
//! - `MutateParam`   — perturb a parameter (e.g. swap the substitution
//!                     `value` of `SubstituteValue`, change the `target`
//!                     expression of `RearrangeEquation` to a small
//!                     variant). v1 is conservative; many parameters are
//!                     deliberately not mutated since they're hard to
//!                     re-roll productively.
//!
//! ## Crossover
//!
//! `splice_chains` picks a random cut point in each parent and exchanges
//! the suffix. The resulting children may not execute — they're rejected
//! by the pre-filter rather than repaired.

use crate::cache_bundle::CacheBundle;
use nasrudin_core::{
    axiom_id_from_name, axiom_set_hash, canonical_hash, skeleton_hash, BinOp, Expr, FitnessScore,
    PhysConst,
};
use nasrudin_derive::lean_emitter::{LeanEmitConfig, emit_lean_file};
use nasrudin_derive::lean_verify::{verify_with_cache, LeanVerifier, LeanVerifyResult, VerifyWithCacheCtx};
use nasrudin_derive::{AxiomStore, Chain, DerivationContext, DerivationStrategy, RuleStep};
use nasrudin_rocks::{AttemptsCache, TacticPriorsCache};
use rand::Rng;
use rand::seq::IteratorRandom;
use std::collections::BTreeSet;
use std::path::Path;
use std::sync::atomic::Ordering;

/// Mutate `chain` by exactly one operator chosen uniformly at random.
///
/// `store` is needed for `Insert` / `MutateAxiom` to pick a valid axiom
/// name and for fact-combining target synthesis (`MutateParam` on a
/// `RearrangeEquation`). If the chain is empty, only `Insert` runs.
/// The mutation is purely *syntactic* — no execution check is
/// performed here. Use the pre-filter (`Chain::execute`) to reject
/// chains that don't run.
pub fn mutate_chain(chain: &mut Chain, store: &AxiomStore, rng: &mut impl Rng) {
    mutate_chain_weighted(chain, store, rng, None);
}

/// Operator names accepted in the `MutationPriors` map. Anything else
/// is silently ignored so an LLM hallucinating an op-name doesn't
/// wedge the GA — the empty / unmatched case falls back to uniform.
pub const MUTATION_OPS: &[&str] = &[
    "insert_random",
    "delete_random",
    "swap_adjacent",
    "mutate_axiom_name",
    "mutate_param",
    "append_productive_suffix",
];

/// Weighted operator selection. Phase E plumbs an LLM-supplied
/// `mutation_priors` map (operator name → weight in [0, 1]) here; when
/// `priors` is `None` or contains no recognised keys, falls back to the
/// historical uniform 1/6 distribution.
pub fn mutate_chain_weighted(
    chain: &mut Chain,
    store: &AxiomStore,
    rng: &mut impl Rng,
    priors: Option<&std::collections::HashMap<String, f32>>,
) {
    mutate_chain_weighted_with_suffix_bias(chain, store, rng, priors, 0.0);
}

/// Same as [`mutate_chain_weighted`] but additionally honors the
/// `suffix_bias` knob from the LLM cluster steerer's `MutationKnobs`.
/// `suffix_bias ∈ [0.0, 1.0]` (clamped) multiplies the
/// `append_productive_suffix` operator's weight by
/// `(1.0 + 4.0 * suffix_bias)` — so `1.0` makes that op 5× more likely
/// than uniform, `0.0` is no bias. Combines multiplicatively with any
/// `mutation_priors` weight already on `append_productive_suffix`.
pub fn mutate_chain_weighted_with_suffix_bias(
    chain: &mut Chain,
    store: &AxiomStore,
    rng: &mut impl Rng,
    priors: Option<&std::collections::HashMap<String, f32>>,
    suffix_bias: f32,
) {
    if chain.is_empty() {
        insert_random(chain, store, rng);
        return;
    }
    let weights = resolve_weights(priors, suffix_bias);
    let pick = weighted_pick(&weights, rng);
    match pick {
        0 => insert_random(chain, store, rng),
        1 => delete_random(chain, rng),
        2 => swap_adjacent(chain, rng),
        3 => mutate_axiom_name(chain, store, rng),
        4 => mutate_param(chain, store, rng),
        _ => append_productive_suffix(chain, store, rng),
    }
}

fn resolve_weights(
    priors: Option<&std::collections::HashMap<String, f32>>,
    suffix_bias: f32,
) -> [f32; 6] {
    let bias = suffix_bias.clamp(0.0, 1.0);
    let suffix_mult = 1.0 + 4.0 * bias;
    let mut w = [1.0f32; 6]; // uniform fallback
    if let Some(map) = priors {
        let mut any = false;
        for (i, &name) in MUTATION_OPS.iter().enumerate() {
            if let Some(&v) = map.get(name) {
                if v.is_finite() && v >= 0.0 {
                    w[i] = v;
                    any = true;
                }
            }
        }
        if !any {
            w = [1.0f32; 6];
        }
        let sum: f32 = w.iter().sum();
        if sum <= 0.0 {
            w = [1.0f32; 6];
        }
    }
    // append_productive_suffix is the last operator (index 5).
    // Multiply AFTER prior resolution so the LLM's priors and the
    // steerer's suffix_bias compose multiplicatively.
    w[5] *= suffix_mult;
    w
}

fn weighted_pick(weights: &[f32; 6], rng: &mut impl Rng) -> u8 {
    let sum: f32 = weights.iter().sum();
    let mut r = rng.random_range(0.0f32..sum);
    for (i, &w) in weights.iter().enumerate() {
        if r < w {
            return i as u8;
        }
        r -= w;
    }
    5
}

/// Test hook: expose the internal weight-resolution path so the
/// integration test can assert the LLM's mutation_priors actually
/// shape the operator-selection distribution. Not for production use.
#[doc(hidden)]
pub fn resolve_weights_for_test(
    priors: Option<&std::collections::HashMap<String, f32>>,
    suffix_bias: f32,
) -> [f32; 6] {
    resolve_weights(priors, suffix_bias)
}

/// Test hook: see `resolve_weights_for_test`.
#[doc(hidden)]
pub fn weighted_pick_for_test(weights: &[f32; 6], rng: &mut impl Rng) -> u8 {
    weighted_pick(weights, rng)
}

/// **Phase 6.5.8** — append a `RearrangeEquation{X²=Y²}` followed by
/// `TakePositiveRoot` to the chain. `X`, `Y` are sampled from the
/// chain's existing fact LHS/RHS atoms, so the synthesized target
/// is grounded in the running context.
///
/// No-op if the chain already ends with `TakePositiveRoot` (we don't
/// stack roots). No-op if the chain has no facts to pull atoms from.
fn append_productive_suffix(chain: &mut Chain, store: &AxiomStore, rng: &mut impl Rng) {
    if matches!(chain.0.last(), Some(RuleStep::TakePositiveRoot)) {
        return;
    }
    let facts = collect_chain_facts(chain, store);
    if facts.is_empty() {
        return;
    }

    // **Iter 24 enrichment:** sample X and Y from a hybrid pool:
    // 60 % chance of fact-side atom (LHS or RHS of an existing fact —
    // always derivable), 40 % chance of physics-shape compound (from
    // the same library used by `random_atom_expr`). The compounds
    // give the suffix mutation access to expressions like `m · c²`,
    // `m² · c²`, `c · p0` that don't appear directly as fact atoms
    // but ARE the building blocks for cross-axiom theorems like
    // `E² = (m·c²)²`. Without this hybrid, the suffix can only
    // synthesise targets that are already direct consequences of
    // single facts (e.g. squaring `c·p0 = E` → `(c·p0)² = E²` →
    // take-root → `c·p0 = E` — a cycle).
    let pool: Vec<&Expr> = facts
        .iter()
        .flat_map(|(_, expr)| {
            if let Expr::BinOp(BinOp::Eq, lhs, rhs) = expr {
                vec![lhs.as_ref(), rhs.as_ref()]
            } else {
                vec![]
            }
        })
        .collect();
    if pool.is_empty() {
        return;
    }
    let x: Expr = if rng.random_bool(0.4) {
        random_physics_compound(rng)
    } else {
        (*pool.iter().choose(rng).unwrap()).clone()
    };
    let y: Expr = if rng.random_bool(0.4) {
        random_physics_compound(rng)
    } else {
        (*pool.iter().choose(rng).unwrap()).clone()
    };

    let two = Expr::Lit(2, 1);
    let x_sq = Expr::BinOp(BinOp::Pow, Box::new(x), Box::new(two.clone()));
    let y_sq = Expr::BinOp(BinOp::Pow, Box::new(y), Box::new(two));
    let target = Expr::BinOp(BinOp::Eq, Box::new(x_sq), Box::new(y_sq));

    chain.push(RuleStep::RearrangeEquation {
        description: "Suffix: X²=Y² for take-root".into(),
        target,
    });
    chain.push(RuleStep::TakePositiveRoot);
}

fn insert_random(chain: &mut Chain, store: &AxiomStore, rng: &mut impl Rng) {
    let facts = collect_chain_facts(chain, store);
    let step = random_step(store, &facts, rng);
    let pos = if chain.is_empty() {
        0
    } else {
        rng.random_range(0..=chain.len())
    };
    chain.0.insert(pos, step);
}

fn delete_random(chain: &mut Chain, rng: &mut impl Rng) {
    if chain.len() <= 1 {
        // Don't drain to empty; an empty chain can't `execute`.
        return;
    }
    let pos = rng.random_range(0..chain.len());
    chain.0.remove(pos);
}

fn swap_adjacent(chain: &mut Chain, rng: &mut impl Rng) {
    if chain.len() < 2 {
        return;
    }
    let pos = rng.random_range(0..chain.len() - 1);
    chain.0.swap(pos, pos + 1);
}

fn mutate_axiom_name(chain: &mut Chain, store: &AxiomStore, rng: &mut impl Rng) {
    let axiom_steps: Vec<usize> = chain
        .0
        .iter()
        .enumerate()
        .filter_map(|(i, s)| match s {
            RuleStep::IntroduceAxiom { .. } => Some(i),
            _ => None,
        })
        .collect();
    let Some(&i) = axiom_steps.iter().choose(rng) else {
        return;
    };
    // Two-stage: pick across hot+cold by index to avoid a 195 k-name
    // Vec allocation per mutation.
    let hot_names = store.iter_hot_names();
    let cold_names = store.cold_names();
    let total = hot_names.len() + cold_names.len();
    if total == 0 {
        return;
    }
    let idx = rng.random_range(0..total);
    let new_name = if idx < hot_names.len() {
        hot_names[idx].clone()
    } else {
        cold_names[idx - hot_names.len()].clone()
    };
    chain.0[i] = RuleStep::IntroduceAxiom {
        axiom_name: new_name,
    };
}

fn mutate_param(chain: &mut Chain, store: &AxiomStore, rng: &mut impl Rng) {
    // Pick a step with mutatable parameters and tweak it.
    let pos = rng.random_range(0..chain.len());
    match &chain.0[pos] {
        RuleStep::SubstituteValue { var, .. } => {
            // Cycle the substitution variable through a small physics-vocab
            // ring.
            let new_var = match var.as_str() {
                "p" | "psq" => "p0".to_string(),
                "p0" => "psq".to_string(),
                other => other.to_string(),
            };
            if let RuleStep::SubstituteValue { var, .. } = &mut chain.0[pos] {
                *var = new_var;
            }
        }
        RuleStep::RearrangeEquation { .. } => {
            // Phase 6.5.4: target synthesis from existing facts. We
            // collect the axiom statements that this chain has loaded
            // so far and combine them via algebraic transformations.
            // This shrinks the target space from O(atom_tree) to
            // O(facts²) and biases targets toward expressions actually
            // derivable by `nlinarith` from the chain's hypotheses.
            let facts = collect_chain_facts(chain, store);
            let new_target = synthesize_target_from_facts(&facts, rng);
            if let RuleStep::RearrangeEquation {
                description, target, ..
            } = &mut chain.0[pos]
            {
                *description = "Synthesised from facts".into();
                *target = new_target;
            }
        }
        _ => {}
    }
}

/// Collect (axiom_name, statement) pairs for every `IntroduceAxiom`
/// step in `chain`, by resolving names via `store`. Used by mutation
/// to do fact-combining target synthesis.
///
/// Returns owned `(String, Expr)` tuples — the cold-tier
/// `AxiomStore::get` decodes fresh from RocksDB so there's no stable
/// borrow lifetime to thread through. The clones are cheap relative
/// to the chain-mutation work that consumes the facts.
fn collect_chain_facts(
    chain: &Chain,
    store: &AxiomStore,
) -> Vec<(String, Expr)> {
    chain
        .0
        .iter()
        .filter_map(|step| match step {
            RuleStep::IntroduceAxiom { axiom_name } => {
                store.get(axiom_name).map(|ax| (axiom_name.clone(), ax.statement))
            }
            _ => None,
        })
        .collect()
}

/// Synthesise a `RearrangeEquation` target by combining the existing
/// chain facts via algebraic transformations.
///
/// **Phase 6.5.4** — this replaces the depth-2 random-atom synthesis
/// (`synthesize_physics_target`) for inserted RearrangeEquation
/// targets where the chain already has facts available. Fact-combining
/// targets are *much* more likely to be derivable by `nlinarith`
/// because they are linear/polynomial combinations of existing
/// hypotheses.
///
/// Operators:
/// - `same`: target = fact (trivial; baseline).
/// - `square`: `a = b` → `a² = b²`.
/// - `multc²`: `a = b` → `a·c² = b·c²`.
/// - `multpair`: `a = b ∧ c = d` → `a·c = b·d`.
/// - `transitivity`: `a = b ∧ a = c` → `b = c` (or rotated).
/// - `swap`: `a = b` → `b = a`.
///
/// Falls back to atom-random synthesis when no facts are available.
pub fn synthesize_target_from_facts(facts: &[(String, Expr)], rng: &mut impl Rng) -> Expr {
    if facts.is_empty() {
        return synthesize_physics_target(rng);
    }

    let pick = rng.random_range(0..6u8);
    match pick {
        // same
        0 => {
            let (_, expr) = facts.iter().choose(rng).unwrap();
            expr.clone()
        }
        // square
        1 => {
            let (_, expr) = facts.iter().choose(rng).unwrap();
            if let Expr::BinOp(BinOp::Eq, lhs, rhs) = expr {
                let two = Expr::Lit(2, 1);
                Expr::BinOp(
                    BinOp::Eq,
                    Box::new(Expr::BinOp(
                        BinOp::Pow,
                        Box::new((**lhs).clone()),
                        Box::new(two.clone()),
                    )),
                    Box::new(Expr::BinOp(
                        BinOp::Pow,
                        Box::new((**rhs).clone()),
                        Box::new(two),
                    )),
                )
            } else {
                expr.clone()
            }
        }
        // mult by c²
        2 => {
            let (_, expr) = facts.iter().choose(rng).unwrap();
            if let Expr::BinOp(BinOp::Eq, lhs, rhs) = expr {
                let c = Expr::Const(PhysConst::SpeedOfLight);
                let two = Expr::Lit(2, 1);
                let c_sq = Expr::BinOp(BinOp::Pow, Box::new(c), Box::new(two));
                Expr::BinOp(
                    BinOp::Eq,
                    Box::new(Expr::BinOp(
                        BinOp::Mul,
                        Box::new((**lhs).clone()),
                        Box::new(c_sq.clone()),
                    )),
                    Box::new(Expr::BinOp(
                        BinOp::Mul,
                        Box::new((**rhs).clone()),
                        Box::new(c_sq),
                    )),
                )
            } else {
                expr.clone()
            }
        }
        // mult-pair: (a = b) ∧ (c = d) → a·c = b·d
        3 => {
            if facts.len() >= 2 {
                let (_, f1) = facts.iter().choose(rng).unwrap();
                let (_, f2) = facts.iter().choose(rng).unwrap();
                if let (
                    Expr::BinOp(BinOp::Eq, l1, r1),
                    Expr::BinOp(BinOp::Eq, l2, r2),
                ) = (f1, f2)
                {
                    return Expr::BinOp(
                        BinOp::Eq,
                        Box::new(Expr::BinOp(
                            BinOp::Mul,
                            Box::new((**l1).clone()),
                            Box::new((**l2).clone()),
                        )),
                        Box::new(Expr::BinOp(
                            BinOp::Mul,
                            Box::new((**r1).clone()),
                            Box::new((**r2).clone()),
                        )),
                    );
                }
            }
            facts[0].1.clone()
        }
        // transitivity: try matching equal sides between two facts.
        4 => {
            if facts.len() >= 2 {
                let (_, f1) = facts.iter().choose(rng).unwrap();
                let (_, f2) = facts.iter().choose(rng).unwrap();
                if let (
                    Expr::BinOp(BinOp::Eq, l1, r1),
                    Expr::BinOp(BinOp::Eq, l2, r2),
                ) = (f1, f2)
                {
                    if l1 == l2 {
                        return Expr::BinOp(
                            BinOp::Eq,
                            Box::new((**r1).clone()),
                            Box::new((**r2).clone()),
                        );
                    }
                    if r1 == r2 {
                        return Expr::BinOp(
                            BinOp::Eq,
                            Box::new((**l1).clone()),
                            Box::new((**l2).clone()),
                        );
                    }
                    if l1 == r2 {
                        return Expr::BinOp(
                            BinOp::Eq,
                            Box::new((**l2).clone()),
                            Box::new((**r1).clone()),
                        );
                    }
                }
            }
            facts[0].1.clone()
        }
        // swap: a = b → b = a
        _ => {
            let (_, expr) = facts.iter().choose(rng).unwrap();
            if let Expr::BinOp(BinOp::Eq, lhs, rhs) = expr {
                Expr::BinOp(BinOp::Eq, Box::new((**rhs).clone()), Box::new((**lhs).clone()))
            } else {
                expr.clone()
            }
        }
    }
}

/// Synthesise a physics-shaped equation `Expr` for use as the target
/// of a `RearrangeEquation` step.
///
/// **Phase 6.5.1.** The target needs to be:
///  - A `BinOp::Eq` (equation form),
///  - Built from SR-relevant atoms (`E`, `m`, `c`, `p0`, `psq`, `Msq`,
///    plus small literals),
///  - Of bounded depth (≤ 3) so the search space stays tractable.
///
/// We sample from a small library of structural templates — each
/// template is a *shape* (e.g., `?lhs² = ?rhs²`, `?a = ?b * ?c`) that
/// gets filled with random atoms. This is *generic*: the templates do
/// not encode E=mc² or any specific theorem; they encode the kinds of
/// algebraic relationships that physics theorems take. With nlinarith
/// + sq_nonneg hints handling the proof obligation, the GA only needs
/// to *eventually* sample a target that happens to be derivable from
/// the current chain's facts. For the upstream rest-energy chain, the
/// derivable target is `E^2 = (m*c^2)^2`, which fits the
/// `?lhs² = ?rhs²` template with `?lhs = E` and `?rhs = m*c^2`.
pub fn synthesize_physics_target(rng: &mut impl Rng) -> Expr {
    let lhs = random_atom_expr(rng, 2);
    let rhs = random_atom_expr(rng, 2);
    let pick = rng.random_range(0..5u8);
    let two = Expr::Lit(2, 1);
    match pick {
        // ?lhs² = ?rhs²  (most useful — feeds TakePositiveRoot)
        0 | 1 => Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::BinOp(BinOp::Pow, Box::new(lhs), Box::new(two.clone()))),
            Box::new(Expr::BinOp(BinOp::Pow, Box::new(rhs), Box::new(two))),
        ),
        // ?lhs = ?rhs
        2 => Expr::BinOp(BinOp::Eq, Box::new(lhs), Box::new(rhs)),
        // ?a = ?b * ?c
        3 => {
            let b = random_atom_expr(rng, 1);
            let c = random_atom_expr(rng, 1);
            Expr::BinOp(
                BinOp::Eq,
                Box::new(lhs),
                Box::new(Expr::BinOp(BinOp::Mul, Box::new(b), Box::new(c))),
            )
        }
        // ?lhs² = ?a * ?b² + ?c
        _ => {
            let lhs_sq = Expr::BinOp(BinOp::Pow, Box::new(lhs), Box::new(two.clone()));
            let a = random_atom_expr(rng, 1);
            let b = random_atom_expr(rng, 1);
            let bsq = Expr::BinOp(BinOp::Pow, Box::new(b), Box::new(two));
            let prod = Expr::BinOp(BinOp::Mul, Box::new(a), Box::new(bsq));
            let c = random_atom_expr(rng, 1);
            let sum = Expr::BinOp(BinOp::Add, Box::new(prod), Box::new(c));
            Expr::BinOp(BinOp::Eq, Box::new(lhs_sq), Box::new(sum))
        }
    }
}

/// Generate a random "atom" Expr at most `depth` levels deep using SR-
/// relevant variables, the speed-of-light constant, and small literals.
///
/// **Phase 7+ (iter 23):** when picking a leaf, with 40 % probability
/// we draw from a *physics-shape compound pool* instead — small
/// pre-built compounds like `m · c²`, `c · p0`, `p0²`, `m² · c²` that
/// appear ubiquitously in SR/EM derivations. This is generic (the
/// compounds aren't theorem-specific) but it dramatically improves
/// the probability of synthesising targets like `E² = (m·c²)²` in
/// the chain-based GA.
fn random_atom_expr(rng: &mut impl Rng, depth: u32) -> Expr {
    if depth == 0 || rng.random_bool(0.5) {
        // Leaf or compound from the physics-shape pool.
        if rng.random_bool(0.4) {
            return random_physics_compound(rng);
        }
        let pick = rng.random_range(0..10u8);
        return match pick {
            0 => Expr::Var("E".into()),
            1 => Expr::Var("m".into()),
            2 => Expr::Var("p0".into()),
            3 => Expr::Var("psq".into()),
            4 => Expr::Var("Msq".into()),
            5 => Expr::Const(PhysConst::SpeedOfLight),
            6 => Expr::Lit(1, 1),
            7 => Expr::Lit(2, 1),
            8 => Expr::Lit(0, 1),
            _ => Expr::Var("E".into()),
        };
    }
    // Compound.
    let l = random_atom_expr(rng, depth - 1);
    let r = random_atom_expr(rng, depth - 1);
    let pick = rng.random_range(0..4u8);
    match pick {
        0 => Expr::BinOp(BinOp::Mul, Box::new(l), Box::new(r)),
        1 => Expr::BinOp(BinOp::Add, Box::new(l), Box::new(r)),
        2 => Expr::BinOp(BinOp::Sub, Box::new(l), Box::new(r)),
        _ => Expr::BinOp(BinOp::Pow, Box::new(l), Box::new(r)),
    }
}

/// Pre-built physics-shape compound atoms.
///
/// Generic compounds that appear in many SR/EM derivations. Including
/// these in the atom pool dramatically increases the chance that
/// random target synthesis produces an `X² = Y²` target whose
/// (X, Y) pair is derivable by `nlinarith` from the chain's facts.
/// E.g., for `E = m·c²`, the GA needs to sample target
/// `E² = (m·c²)²`; with `m·c²` in the compound pool that probability
/// is O(1/N), instead of O((1/atoms)^depth) for raw atom sampling.
fn random_physics_compound(rng: &mut impl Rng) -> Expr {
    let two = Expr::Lit(2, 1);
    let m = Expr::Var("m".into());
    let p0 = Expr::Var("p0".into());
    let c = Expr::Const(PhysConst::SpeedOfLight);
    let e = Expr::Var("E".into());
    let psq = Expr::Var("psq".into());

    let pick = rng.random_range(0..8u8);
    match pick {
        // m · c²
        0 => Expr::BinOp(
            BinOp::Mul,
            Box::new(m.clone()),
            Box::new(Expr::BinOp(BinOp::Pow, Box::new(c.clone()), Box::new(two.clone()))),
        ),
        // c · p0
        1 => Expr::BinOp(BinOp::Mul, Box::new(c.clone()), Box::new(p0.clone())),
        // p0²
        2 => Expr::BinOp(BinOp::Pow, Box::new(p0.clone()), Box::new(two.clone())),
        // m² · c²
        3 => Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::BinOp(BinOp::Pow, Box::new(m.clone()), Box::new(two.clone()))),
            Box::new(Expr::BinOp(BinOp::Pow, Box::new(c.clone()), Box::new(two.clone()))),
        ),
        // E²
        4 => Expr::BinOp(BinOp::Pow, Box::new(e.clone()), Box::new(two.clone())),
        // p0² − psq
        5 => Expr::BinOp(
            BinOp::Sub,
            Box::new(Expr::BinOp(BinOp::Pow, Box::new(p0.clone()), Box::new(two.clone()))),
            Box::new(psq.clone()),
        ),
        // m · c
        6 => Expr::BinOp(BinOp::Mul, Box::new(m.clone()), Box::new(c.clone())),
        // c²
        _ => Expr::BinOp(BinOp::Pow, Box::new(c), Box::new(two)),
    }
}

fn random_step(store: &AxiomStore, facts: &[(String, Expr)], rng: &mut impl Rng) -> RuleStep {
    // Weighted: most steps are IntroduceAxiom; the rest split between
    // the four transforming rules. RearrangeEquation gets a *fact-
    // combining* target (Phase 6.5.4) when facts are available, falling
    // back to random atom synthesis (6.5.1) otherwise.
    let pick = rng.random_range(0..8u8);
    match pick {
        0 | 1 | 2 => {
            // Two-stage pick to avoid materializing 195 k cold-tier
            // names on every mutation. Hot names allocate a fresh
            // Vec each call; cold names are a `&[String]` reference
            // into the AxiomStore's preallocated snapshot.
            let hot_names = store.iter_hot_names();
            let cold_names = store.cold_names();
            let total = hot_names.len() + cold_names.len();
            if total == 0 {
                return RuleStep::AlgebraicSimplify;
            }
            let idx = rng.random_range(0..total);
            let name = if idx < hot_names.len() {
                hot_names[idx].clone()
            } else {
                cold_names[idx - hot_names.len()].clone()
            };
            RuleStep::IntroduceAxiom { axiom_name: name }
        }
        3 => RuleStep::AlgebraicSimplify,
        4 => RuleStep::TakePositiveRoot,
        5 => RuleStep::SubstituteValue {
            var: "psq".into(),
            value: nasrudin_core::Expr::Lit(0, 1),
            reason: "rest_frame".into(),
        },
        _ => RuleStep::RearrangeEquation {
            description: "Synthesised target".into(),
            target: synthesize_target_from_facts(facts, rng),
        },
    }
}

/// A `Chain` wrapped with NSGA-II metadata and fitness.
///
/// Phase 5.2 of the project plan. The chain-based GA evolves
/// `ChainIndividual`s through the same NSGA-II pipeline used by the
/// AST-tree GA — selection by Pareto rank + crowding distance,
/// fitness from `evaluate_chain_fitness`, mutation via `mutate_chain`,
/// crossover via `splice_chains`.
#[derive(Debug, Clone)]
pub struct ChainIndividual {
    pub chain: Chain,
    pub fitness: FitnessScore,
    pub pareto_rank: usize,
    pub crowding_distance: f64,
    /// Per-cluster routing tag. Populated by the worker after
    /// clustering the seed population at chunk start; inherited
    /// from `parent_a` during crossover so per-cluster mutation
    /// rates apply to children of a cluster too. `0` is the
    /// default (and acts as the "unclustered" id since the GA
    /// runs unmodified when `cluster_multipliers` is empty).
    pub cluster_id: u32,
}

impl ChainIndividual {
    pub fn new(chain: Chain, fitness: FitnessScore) -> Self {
        Self {
            chain,
            fitness,
            pareto_rank: usize::MAX,
            crowding_distance: 0.0,
            cluster_id: 0,
        }
    }

    pub fn with_cluster(chain: Chain, fitness: FitnessScore, cluster_id: u32) -> Self {
        Self {
            chain,
            fitness,
            pareto_rank: usize::MAX,
            crowding_distance: 0.0,
            cluster_id,
        }
    }
}

/// Outcome of running a chain through `DerivationContext`.
#[derive(Debug, Clone)]
pub struct ChainEvalResult {
    pub executes: bool,
    pub depth: u32,
    pub final_expr: Option<nasrudin_core::Expr>,
    pub steps_run: usize,
}

/// Run the chain through a fresh `DerivationContext` and report.
///
/// Used by `evaluate_chain_fitness` and as the GA's pre-filter: if
/// `executes` is false, the candidate is rejected before it reaches the
/// Lean verifier.
pub fn evaluate_chain(chain: &Chain, store: &AxiomStore) -> ChainEvalResult {
    let mut ctx = DerivationContext::new();
    let res = chain.execute(store, &mut ctx);
    ChainEvalResult {
        executes: res.is_ok(),
        depth: ctx.steps().len() as u32,
        final_expr: res.ok(),
        steps_run: ctx.steps().len(),
    }
}

/// Compute a `FitnessScore` for a chain individual.
///
/// Multi-objective scoring (NSGA-II — higher is better for each axis):
/// - **novelty**: 1.0 if the chain executes; 0.0 otherwise. (Pre-filter
///   surrogate; verified theorems get a Lean-side bump elsewhere.)
/// - **complexity**: `1 / (1 + steps)` — prefer terse derivations.
/// - **depth**: `min(steps / 8, 1.0)` — reward derivations of substantial
///   length but cap at 8 steps to avoid pathological growth.
/// - **dimensional**: 1.0 if the final expression has homogeneous
///   dimensions (deferred to v2; placeholder 0.5 for now).
/// - **symmetry**: 0.5 placeholder (Lorentz-symmetry detector is a
///   v2 enhancement).
/// - **connectivity**: count of distinct axioms referenced by chain
///   `IntroduceAxiom` steps, normalised by 4.
/// - **nasrudin_relevance**: 1.0 if the final expression is an equation
///   (`BinOp::Eq`), else 0.0. Most physics theorems are equations.
pub fn evaluate_chain_fitness(chain: &Chain, store: &AxiomStore) -> FitnessScore {
    evaluate_chain_fitness_with_target(chain, store, None)
}

/// Like [`evaluate_chain_fitness`] but additionally scores the chain's
/// final expression against a target shape and (optionally) a sub-goal
/// ladder. The target signals stay zero when no `target` is given —
/// behaviour identical to the old one-arg form.
pub fn evaluate_chain_fitness_with_target(
    chain: &Chain,
    store: &AxiomStore,
    target: Option<&crate::target::TargetSpec>,
) -> FitnessScore {
    let eval = evaluate_chain(chain, store);
    let executes = if eval.executes { 1.0 } else { 0.0 };
    let steps = eval.steps_run as f64;
    let depth_score = (steps / 8.0).min(1.0);
    let complexity = 1.0 / (1.0 + steps);

    // Distinct axiom names invoked.
    use std::collections::BTreeSet;
    let distinct_axioms: BTreeSet<&String> = chain
        .0
        .iter()
        .filter_map(|s| match s {
            RuleStep::IntroduceAxiom { axiom_name } => Some(axiom_name),
            _ => None,
        })
        .collect();
    let connectivity = (distinct_axioms.len() as f64 / 4.0).min(1.0);

    let is_eq = matches!(
        eval.final_expr,
        Some(nasrudin_core::Expr::BinOp(nasrudin_core::BinOp::Eq, _, _))
    );
    let relevance = if is_eq { 1.0 } else { 0.0 };

    let (target_shape, ladder_progress) = match (&eval.final_expr, target) {
        (Some(expr), Some(spec)) => (
            crate::target::shape_similarity(expr, &spec.final_target),
            crate::target::ladder_score(expr, spec),
        ),
        _ => (0.0, 0.0),
    };

    FitnessScore {
        novelty: executes,
        complexity,
        depth: depth_score,
        dimensional: 0.5, // v2: thread `infer_dimension` here.
        symmetry: 0.5,    // v2: detect Lorentz invariance.
        connectivity,
        nasrudin_relevance: relevance,
        target_shape,
        ladder_progress,
    }
}

/// Verification outcome for a chain.
#[derive(Debug, Clone)]
pub enum ChainVerifyOutcome {
    /// Chain ran, Lean accepted the proof. The .lean source is the
    /// `proof_term`.
    Verified { lean_source: String, module_path: String },
    /// Chain ran, but Lean rejected the proof.
    LeanRejected { lean_source: String, stderr: String },
    /// Chain failed the pre-filter (didn't execute).
    PreFilterFailed { reason: String },
    /// Lean toolchain wasn't reachable.
    ToolchainError { message: String },
}

/// Outcome of one round-trip to the persistent Lean elaborator.
enum PersistentOutcome {
    /// Elaborator accepted the candidate (kernel verdict).
    Verified,
    /// Elaborator rejected with a diagnostic.
    Rejected { stderr: String },
    /// RPC error / timeout / `Fatal` reply — caller should fall back
    /// to the legacy `lake build` path.
    FellBack { reason: String },
}

/// Synchronously call the persistent elaborator from inside a tokio
/// runtime. The verify path is sync today (mirrors `lake build`); we
/// reuse the worker's tokio handle to drive the async RPC.
///
/// `block_in_place` is required: `Handle::block_on` from inside a tokio
/// worker thread panics with "Cannot start a runtime from within a
/// runtime." `block_in_place` lets the multi-thread runtime relocate
/// the current task's siblings to other workers while we block here.
/// Was never observed before the elaborator daemon shipped because the
/// in-process spawn path failed at boot on the 2 GB droplet, so
/// `call_persistent_elaborate` was never reached — the bug lay dormant
/// behind a never-firing code path.
fn call_persistent_elaborate(
    elab: &nasrudin_lean_bridge::PersistentElaborator,
    source: &str,
) -> PersistentOutcome {
    use nasrudin_lean_bridge::persistent_protocol::Response;
    let handle = match tokio::runtime::Handle::try_current() {
        Ok(h) => h,
        Err(e) => {
            return PersistentOutcome::FellBack {
                reason: format!("no tokio runtime: {e}"),
            };
        }
    };
    let result = tokio::task::block_in_place(|| handle.block_on(elab.elaborate(source)));
    match result {
        Ok(Response::ElaborateOk { .. }) => PersistentOutcome::Verified,
        Ok(Response::ElaborateError { message, .. }) => {
            PersistentOutcome::Rejected { stderr: message }
        }
        Ok(Response::Fatal { message }) => PersistentOutcome::FellBack {
            reason: format!("fatal: {message}"),
        },
        Ok(other) => PersistentOutcome::FellBack {
            reason: format!("unexpected response: {other:?}"),
        },
        Err(e) => PersistentOutcome::FellBack {
            reason: format!("rpc error: {e}"),
        },
    }
}

/// Run a chain end-to-end: pre-filter via `Chain::execute`, emit Lean
/// via the generic emitter, lake-build via `LeanVerifier`. Returns the
/// outcome (pre-filter rejection, Lean rejection, or success with the
/// emitted .lean source as the proof witness).
///
/// The `module_basename` is appended to `PhysicsGenerator.Derived.` to
/// form the full Lean module path; the verifier will write a file at
/// `<prover_root>/PhysicsGenerator/Derived/<module_basename>.lean` and
/// run `lake build` on it. Use a unique basename per call (e.g. include
/// a hash) to avoid file collisions when verifying many candidates.
pub fn verify_chain(
    chain: &Chain,
    store: &AxiomStore,
    prover_root: impl AsRef<Path>,
    module_basename: &str,
    theorem_name: &str,
) -> ChainVerifyOutcome {
    verify_chain_cached(chain, store, prover_root, module_basename, theorem_name, None)
}

/// Cache-aware variant of [`verify_chain`].
///
/// When `bundle` is `Some`, the lake-build path goes through the
/// `attempts` cache (skip on hit, write on miss) and on success
/// records the winning module name into `tactic_priors`. When
/// `None`, behaves identically to [`verify_chain`].
pub fn verify_chain_cached(
    chain: &Chain,
    store: &AxiomStore,
    prover_root: impl AsRef<Path>,
    module_basename: &str,
    theorem_name: &str,
    bundle: Option<&CacheBundle>,
) -> ChainVerifyOutcome {
    verify_chain_cached_full(
        chain,
        store,
        prover_root,
        module_basename,
        theorem_name,
        bundle,
        None,
    )
}

/// Full variant accepting an optional persistent Lean elaborator.
///
/// When `elaborator` is `Some`, the verify path tries the warm Lean
/// elaborator first (~100–500ms per candidate); on RPC error or
/// elaborator timeout, falls back to the legacy `lake build` path.
/// When `None`, behaves identically to [`verify_chain_cached`].
#[allow(clippy::too_many_arguments)]
pub fn verify_chain_cached_full(
    chain: &Chain,
    store: &AxiomStore,
    prover_root: impl AsRef<Path>,
    module_basename: &str,
    theorem_name: &str,
    bundle: Option<&CacheBundle>,
    elaborator: Option<&std::sync::Arc<nasrudin_lean_bridge::PersistentElaborator>>,
) -> ChainVerifyOutcome {
    // Pre-filter: run the chain.
    let mut ctx = DerivationContext::new();
    if let Err(e) = chain.execute(store, &mut ctx) {
        return ChainVerifyOutcome::PreFilterFailed {
            reason: format!("{e}"),
        };
    }
    let final_expr = match ctx.current() {
        Some(e) => e.clone(),
        None => {
            return ChainVerifyOutcome::PreFilterFailed {
                reason: "chain produced no current expression".into(),
            };
        }
    };

    // Emit Lean via the generic emitter.
    let cfg = LeanEmitConfig {
        namespace: "PhysicsGenerator.Derived".into(),
        theorem_name: theorem_name.to_string(),
        use_mathlib: true,
    };
    let lean_source = emit_lean_file(&ctx, &cfg);
    let module_path = format!("PhysicsGenerator.Derived.{module_basename}");

    let verifier = LeanVerifier::new(prover_root.as_ref());

    // Layer 1: try the persistent elaborator first when available.
    // RPC errors / timeouts fall through to the legacy lake-build path
    // below, so an elaborator hiccup never silently drops a candidate.
    if let Some(elab) = elaborator {
        match call_persistent_elaborate(elab.as_ref(), &lean_source) {
            PersistentOutcome::Verified => {
                return ChainVerifyOutcome::Verified {
                    lean_source,
                    module_path,
                };
            }
            PersistentOutcome::Rejected { stderr } => {
                // Elaborator says no — clean up the (not-written) file
                // path is no-op and we trust the kernel verdict.
                return ChainVerifyOutcome::LeanRejected { lean_source, stderr };
            }
            PersistentOutcome::FellBack { reason } => {
                tracing::debug!(
                    "persistent elaborator failed ({reason}); falling back to lake build"
                );
                // Continue to the lake-build path below.
            }
        }
    }

    let outcome = if let Some(b) = bundle {
        // Build the 16-byte cache key: canonical_hash || axiom_set_hash.
        let canonical_str = final_expr.to_canonical();
        let mut canon8 = [0u8; 8];
        let canon_bytes = canonical_hash(&canonical_str);
        canon8.copy_from_slice(&canon_bytes[..8]);

        // Walk chain steps, collect axiom names (and IntroduceTheorem names),
        // hash each into a synthetic 8-byte ID, then BLAKE3 the sorted set.
        let mut axiom_ids: BTreeSet<[u8; 8]> = BTreeSet::new();
        for step in &chain.0 {
            match step {
                RuleStep::IntroduceAxiom { axiom_name } => {
                    axiom_ids.insert(axiom_id_from_name(axiom_name));
                }
                RuleStep::IntroduceTheorem { theorem_name } => {
                    axiom_ids.insert(axiom_id_from_name(theorem_name));
                }
                _ => {}
            }
        }
        let axiom_hash = axiom_set_hash(&axiom_ids);
        let cache_key = AttemptsCache::make_key(&canon8, &axiom_hash);

        // Account hit/miss before calling verify_with_cache (which does its
        // own lookup but doesn't touch CacheStats).
        let pre_hit = b
            .attempts
            .get_with_ttl(&cache_key, chrono::Duration::days(b.ttl_days))
            .ok()
            .flatten()
            .is_some();
        if pre_hit {
            b.stats.attempts_hits.fetch_add(1, Ordering::Relaxed);
        } else {
            b.stats.attempts_misses.fetch_add(1, Ordering::Relaxed);
        }

        let vctx = VerifyWithCacheCtx {
            verifier: &verifier,
            cache: &b.attempts,
            cache_key: &cache_key,
            lean_version: &b.lean_version,
            worker_id: &b.worker_id,
            ttl_days: b.ttl_days,
        };
        let raw = verify_with_cache(&vctx, &lean_source, &module_path);

        // On verifier success, record the module / theorem name as the
        // tactic prior for this goal skeleton. We don't extract a discrete
        // tactic name from `lake build` today; persisting `theorem_name`
        // gives the priors layer something to rank without claiming a
        // specific tactic chain.
        if matches!(raw, LeanVerifyResult::Success) {
            let skel_hash = skeleton_hash(&final_expr);
            let priors_key = TacticPriorsCache::make_key(&skel_hash, &axiom_hash);
            if let Err(e) = b.tactic_priors.record_success(&priors_key, theorem_name, 0) {
                tracing::warn!("tactic_priors record_success failed: {e}");
            }
        }
        raw
    } else {
        verifier.verify_file(&lean_source, &module_path)
    };

    // Iter 17 fix: on Lean rejection or toolchain error, remove the
    // emitted .lean file from the prover directory so it doesn't
    // pollute the workspace with un-verified content. Successful
    // verifications keep the file (for inspection / archival).
    if !matches!(outcome, LeanVerifyResult::Success) {
        let relative = format!("{}.lean", module_path.replace('.', "/"));
        let file_path = prover_root.as_ref().join(&relative);
        let _ = std::fs::remove_file(&file_path);
    }

    match outcome {
        LeanVerifyResult::Success => ChainVerifyOutcome::Verified {
            lean_source,
            module_path,
        },
        LeanVerifyResult::Failed { stderr } => ChainVerifyOutcome::LeanRejected {
            lean_source,
            stderr,
        },
        LeanVerifyResult::ProcessError { message } => ChainVerifyOutcome::ToolchainError { message },
    }
}

/// Splice two chains at a random cut point, returning two children.
pub fn splice_chains(a: &Chain, b: &Chain, rng: &mut impl Rng) -> (Chain, Chain) {
    let cut_a = if a.is_empty() {
        0
    } else {
        rng.random_range(0..=a.len())
    };
    let cut_b = if b.is_empty() {
        0
    } else {
        rng.random_range(0..=b.len())
    };
    let mut child_a = Chain(a.0[..cut_a].to_vec());
    child_a.0.extend_from_slice(&b.0[cut_b..]);
    let mut child_b = Chain(b.0[..cut_b].to_vec());
    child_b.0.extend_from_slice(&a.0[cut_a..]);
    (child_a, child_b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_derive::{AxiomStore, Chain, DerivationContext, DerivationStrategy};

    fn upstream_store() -> AxiomStore {
        let mut s = AxiomStore::new();
        s.load_special_relativity_upstream();
        s
    }

    #[test]
    fn verify_chain_cached_with_empty_chain_pre_filter_rejects() {
        // Smoke test: verify_chain_cached compiles, accepts an
        // Option<&CacheBundle>, and short-circuits the empty chain
        // before any cache or lake-build attempt.
        use crate::cache_bundle::CacheBundle;
        use nasrudin_derive::CacheStats;
        use nasrudin_rocks::{AttemptsCache, TacticPriorsCache};
        use std::sync::Arc;
        use tempfile::tempdir;

        let dir_a = tempdir().unwrap();
        let attempts = Arc::new(AttemptsCache::open(dir_a.path().to_str().unwrap()).unwrap());
        let dir_t = tempdir().unwrap();
        let priors = Arc::new(TacticPriorsCache::open(dir_t.path().to_str().unwrap()).unwrap());
        let bundle = CacheBundle {
            attempts,
            tactic_priors: priors,
            stats: Arc::new(CacheStats::default()),
            lean_version: "4.27.0".into(),
            worker_id: "test".into(),
            ttl_days: 30,
        };
        let store = upstream_store();
        let chain = Chain(vec![]);
        let outcome = verify_chain_cached(
            &chain,
            &store,
            std::path::Path::new("/nonexistent"),
            "test_basename",
            "test_thm",
            Some(&bundle),
        );
        assert!(matches!(outcome, ChainVerifyOutcome::PreFilterFailed { .. }));
    }

    #[test]
    fn mutate_does_not_panic_on_empty() {
        let store = upstream_store();
        let mut chain = Chain::new();
        let mut rng = rand::rng();
        for _ in 0..50 {
            mutate_chain(&mut chain, &store, &mut rng);
        }
        // Should now be non-empty (insert kicks in repeatedly).
        assert!(!chain.is_empty());
    }

    #[test]
    fn mutated_chain_either_executes_or_pre_filters() {
        // Property: after mutation, either the chain runs successfully
        // (producing a current expression) or it fails with a clean
        // DeriveError — never panics.
        let store = upstream_store();
        let seed = Chain::rest_energy_from_upstream();
        let mut rng = rand::rng();
        for trial in 0..100 {
            let mut chain = seed.clone();
            mutate_chain(&mut chain, &store, &mut rng);
            let mut ctx = DerivationContext::new();
            let _ = chain.execute(&store, &mut ctx); // Ok or Err is fine.
            let _ = trial;
        }
    }

    #[test]
    fn splice_lengths_are_compatible() {
        // |child_a| + |child_b| = |a| + |b|
        let mut rng = rand::rng();
        let a = Chain::rest_energy_from_upstream();
        let b = Chain::rest_energy_from_upstream();
        for _ in 0..20 {
            let (ca, cb) = splice_chains(&a, &b, &mut rng);
            assert_eq!(ca.len() + cb.len(), a.len() + b.len());
        }
    }

    /// Heavy: actually runs `lake build`. Requires the prover dir to be
    /// set up (Mathlib cached, RestEnergyUpstream.olean reachable).
    /// Marked `#[ignore]` so it doesn't run in normal `cargo test`.
    #[test]
    #[ignore = "calls lake build (5+ min); run with --ignored"]
    fn upstream_chain_verifies_via_lake() {
        let store = upstream_store();
        let chain = Chain::rest_energy_from_upstream();
        // Use the repo's prover dir relative to engine/crates/ga (tests run
        // from there).
        let prover_root = std::path::PathBuf::from("../../../prover");
        let outcome = verify_chain(
            &chain,
            &store,
            prover_root,
            "ChainTestRestEnergy",
            "rest_energy_chain_test",
        );
        match outcome {
            ChainVerifyOutcome::Verified { .. } => {}
            other => panic!("expected Verified, got {other:?}"),
        }
    }

    #[test]
    fn pre_filter_rejects_broken_chain() {
        let store = upstream_store();
        // Chain referencing a missing axiom. Should fail pre-filter
        // *before* attempting lake build.
        let bad = Chain(vec![RuleStep::IntroduceAxiom {
            axiom_name: "no_such_axiom_xyz".into(),
        }]);
        let outcome = verify_chain(
            &bad,
            &store,
            std::path::PathBuf::from("/nonexistent"),
            "Junk",
            "junk",
        );
        matches!(outcome, ChainVerifyOutcome::PreFilterFailed { .. });
    }

    #[test]
    fn append_productive_suffix_grows_chain() {
        let store = upstream_store();
        let mut rng = rand::rng();
        let mut chain = Chain(vec![
            RuleStep::IntroduceAxiom {
                axiom_name: "four_momentum_time_component".into(),
            },
            RuleStep::IntroduceAxiom {
                axiom_name: "minkowski_invariant_def".into(),
            },
        ]);
        let before = chain.len();
        super::append_productive_suffix(&mut chain, &store, &mut rng);
        // Either grew by exactly 2 (RearrangeEquation + TakePositiveRoot)
        // or stayed the same (already ends in TakePositiveRoot — not the
        // case here).
        assert_eq!(chain.len(), before + 2);
        assert!(matches!(
            chain.0.last(),
            Some(RuleStep::TakePositiveRoot)
        ));
    }

    #[test]
    fn append_productive_suffix_no_op_if_already_root() {
        let store = upstream_store();
        let mut rng = rand::rng();
        let mut chain = Chain(vec![
            RuleStep::IntroduceAxiom {
                axiom_name: "four_momentum_time_component".into(),
            },
            RuleStep::TakePositiveRoot,
        ]);
        let before = chain.len();
        super::append_productive_suffix(&mut chain, &store, &mut rng);
        assert_eq!(chain.len(), before, "shouldn't append after TakePositiveRoot");
    }

    #[test]
    fn fitness_of_seed_chain_executes_and_is_eq() {
        let store = upstream_store();
        let chain = Chain::rest_energy_from_upstream();
        let fit = evaluate_chain_fitness(&chain, &store);
        assert_eq!(fit.novelty, 1.0, "seed chain should execute");
        assert_eq!(fit.nasrudin_relevance, 1.0, "result should be an equation");
        assert!(fit.connectivity > 0.0, "seed uses ≥1 axiom");
    }

    #[test]
    fn fitness_of_empty_chain_is_zero() {
        let store = upstream_store();
        let fit = evaluate_chain_fitness(&Chain::new(), &store);
        assert_eq!(fit.novelty, 0.0);
    }

    #[test]
    fn chain_individual_constructible() {
        let store = upstream_store();
        let chain = Chain::rest_energy_from_upstream();
        let fit = evaluate_chain_fitness(&chain, &store);
        let ind = ChainIndividual::new(chain, fit);
        assert!(!ind.chain.is_empty());
        assert_eq!(ind.pareto_rank, usize::MAX);
    }

    #[test]
    fn upstream_chain_post_mutation_can_still_succeed() {
        // Run many mutations; assert that *at least one* mutated chain
        // still executes (i.e., we haven't broken the search space).
        let store = upstream_store();
        let mut rng = rand::rng();
        let mut any_success = false;
        for _ in 0..200 {
            let mut chain = Chain::rest_energy_from_upstream();
            mutate_chain(&mut chain, &store, &mut rng);
            let mut ctx = DerivationContext::new();
            if chain.execute(&store, &mut ctx).is_ok() {
                any_success = true;
                break;
            }
        }
        assert!(
            any_success,
            "mutation broke the search space — no mutated chain executed in 200 trials"
        );
    }
}
