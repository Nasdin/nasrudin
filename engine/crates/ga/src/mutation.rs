//! Mutation operators for `Expr` trees.
//!
//! Eight mutation operators that introduce controlled variation:
//! VarSwap, OpSwap, AxiomInjection, Simplify, UnaryWrap, UnaryUnwrap,
//! LitPerturb, ConstSwap.
//!
//! ## AxiomInjection and the AxiomStore
//!
//! The `axiom_injection` operator can sample fragments from the live
//! [`AxiomStore`] instead of the legacy 4-fragment hardcoded set when
//! a store is provided via `mutate_with_store`. This is the load-bearing
//! piece that lets a GA running on a QM-domain island reach the
//! Schrödinger / commutator / Born-rule postulates as substrate during
//! evolution. Without this wiring, mutation explores only the 4
//! hardcoded fragments (mc², ℏω, k_B·T, p²/2m) and the AxiomStore is
//! invisible to the population once `seed_from_axioms` runs at t=0.

use nasrudin_core::{BinOp, Expr, PhysConst, UnOp};
use nasrudin_derive::AxiomStore;
use rand::seq::IteratorRandom;
use rand::{Rng, RngExt};

/// Which mutation operator to apply.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MutationOp {
    /// Swap a variable name with another from the domain vocabulary.
    VarSwap,
    /// Replace a binary operator with a different one.
    OpSwap,
    /// Insert a physics axiom fragment as a subtree.
    AxiomInjection,
    /// Simplify: fold constant subexpressions.
    Simplify,
    /// Wrap a subtree with a unary operator.
    UnaryWrap,
    /// Remove a unary operator, exposing its child.
    UnaryUnwrap,
    /// Perturb a literal value by a small amount.
    LitPerturb,
    /// Swap one physical constant for another.
    ConstSwap,
}

const ALL_MUTATIONS: &[MutationOp] = &[
    MutationOp::VarSwap,
    MutationOp::OpSwap,
    MutationOp::AxiomInjection,
    MutationOp::Simplify,
    MutationOp::UnaryWrap,
    MutationOp::UnaryUnwrap,
    MutationOp::LitPerturb,
    MutationOp::ConstSwap,
];

/// Apply a random mutation to an expression.
///
/// Legacy entry point — falls back to the 4-fragment hardcoded
/// AxiomInjection pool. Prefer [`mutate_with_store`] for the GA loop
/// so AxiomInjection samples from the live AxiomStore (incl. all of
/// PhysLean + Mathlib + the foundational postulates).
pub fn mutate(expr: &Expr, rng: &mut impl Rng) -> Expr {
    let op = ALL_MUTATIONS[rng.random_range(0..ALL_MUTATIONS.len())];
    apply_mutation(expr, op, rng)
}

/// Apply a random mutation to an expression with an [`AxiomStore`]
/// available. AxiomInjection samples a random axiom statement from the
/// store (filtered to the current domain when one is provided, then
/// falling back to the full store for cross-domain leverage), which
/// makes math substrate (Mathlib lemmas) and foundational postulates
/// (Schrödinger, Born rule, etc.) reachable during evolution.
///
/// When `domain_hint` is `None` the entire store is in scope. When it
/// is `Some(d)` a 70/30 split is used: 70 % of injections sample from
/// `store.by_domain(d)`, 30 % from any axiom (so cross-domain
/// composition stays possible — e.g. a QM island still benefits from
/// algebraic identities tagged `PureMath`).
pub fn mutate_with_store(
    expr: &Expr,
    store: Option<&AxiomStore>,
    domain_hint: Option<&nasrudin_core::Domain>,
    rng: &mut impl Rng,
) -> Expr {
    let empty: std::collections::HashSet<nasrudin_core::TheoremId> =
        std::collections::HashSet::new();
    mutate_with_store_excluding(expr, store, domain_hint, &empty, rng)
}

/// Like [`mutate_with_store`] but skips any axiom whose synthetic id
/// (derived from its `name` via [`nasrudin_core::axiom_id_from_name`])
/// is in `forbidden`. Used by target-driven evolution to keep the
/// target itself + every theorem that transitively cites it out of the
/// AxiomInjection pool.
pub fn mutate_with_store_excluding(
    expr: &Expr,
    store: Option<&AxiomStore>,
    domain_hint: Option<&nasrudin_core::Domain>,
    forbidden: &std::collections::HashSet<nasrudin_core::TheoremId>,
    rng: &mut impl Rng,
) -> Expr {
    let op = ALL_MUTATIONS[rng.random_range(0..ALL_MUTATIONS.len())];
    apply_mutation_with_store_excluding(expr, op, store, domain_hint, forbidden, rng)
}

/// Apply a specific mutation operator.
pub fn apply_mutation(expr: &Expr, op: MutationOp, rng: &mut impl Rng) -> Expr {
    apply_mutation_with_store(expr, op, None, None, rng)
}

/// Apply a specific mutation operator with an optional [`AxiomStore`]
/// for `AxiomInjection`. All other operators ignore the store.
pub fn apply_mutation_with_store(
    expr: &Expr,
    op: MutationOp,
    store: Option<&AxiomStore>,
    domain_hint: Option<&nasrudin_core::Domain>,
    rng: &mut impl Rng,
) -> Expr {
    let empty: std::collections::HashSet<nasrudin_core::TheoremId> =
        std::collections::HashSet::new();
    apply_mutation_with_store_excluding(expr, op, store, domain_hint, &empty, rng)
}

/// Like [`apply_mutation_with_store`] but threads a forbidden-axiom
/// filter into AxiomInjection. Other operators ignore both `store` and
/// `forbidden`.
pub fn apply_mutation_with_store_excluding(
    expr: &Expr,
    op: MutationOp,
    store: Option<&AxiomStore>,
    domain_hint: Option<&nasrudin_core::Domain>,
    forbidden: &std::collections::HashSet<nasrudin_core::TheoremId>,
    rng: &mut impl Rng,
) -> Expr {
    match op {
        MutationOp::VarSwap => var_swap(expr, rng),
        MutationOp::OpSwap => op_swap(expr, rng),
        MutationOp::AxiomInjection => {
            axiom_injection_with_store(expr, store, domain_hint, forbidden, rng)
        }
        MutationOp::Simplify => simplify(expr),
        MutationOp::UnaryWrap => unary_wrap(expr, rng),
        MutationOp::UnaryUnwrap => unary_unwrap(expr),
        MutationOp::LitPerturb => lit_perturb(expr, rng),
        MutationOp::ConstSwap => const_swap(expr, rng),
    }
}

/// Domain-relevant variable names for physics.
const PHYSICS_VARS: &[&str] = &[
    "E", "m", "c", "p", "v", "t", "F", "a", "x", "r", "T", "S", "k", "h", "q", "V", "I", "R", "B",
    "G", "L", "H", "U", "W", "P", "n", "f", "omega", "lambda", "phi", "theta", "rho", "sigma",
];

/// Swap a random variable with a different one from the physics vocabulary.
fn var_swap(expr: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::Var(name) => {
            let new_name = loop {
                let candidate = PHYSICS_VARS[rng.random_range(0..PHYSICS_VARS.len())];
                if candidate != name {
                    break candidate.to_string();
                }
            };
            Expr::Var(new_name)
        }
        Expr::BinOp(op, l, r) => {
            if rng.random_bool(0.5) {
                Expr::BinOp(op.clone(), Box::new(var_swap(l, rng)), r.clone())
            } else {
                Expr::BinOp(op.clone(), l.clone(), Box::new(var_swap(r, rng)))
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(var_swap(e, rng))),
        other => other.clone(),
    }
}

/// Algebraic binary ops suitable for swapping.
const ALGEBRAIC_OPS: &[BinOp] = &[BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Pow];

/// Replace a binary operator with a different one.
fn op_swap(expr: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::BinOp(op, l, r) => {
            if ALGEBRAIC_OPS.contains(op) {
                let new_op = loop {
                    let candidate = &ALGEBRAIC_OPS[rng.random_range(0..ALGEBRAIC_OPS.len())];
                    if candidate != op {
                        break candidate.clone();
                    }
                };
                Expr::BinOp(new_op, l.clone(), r.clone())
            } else {
                // Recurse into children
                if rng.random_bool(0.5) {
                    Expr::BinOp(op.clone(), Box::new(op_swap(l, rng)), r.clone())
                } else {
                    Expr::BinOp(op.clone(), l.clone(), Box::new(op_swap(r, rng)))
                }
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(op_swap(e, rng))),
        other => other.clone(),
    }
}

/// Inject a small axiom-like fragment into the tree, sampling from a
/// live [`AxiomStore`] when one is provided.
///
/// Selection policy:
///   1. If `store` is `None` or empty → fall back to the 4 hardcoded
///      fragments (legacy behaviour).
///   2. If `domain_hint` is set, sample with probability 0.7 from
///      `store.by_domain(domain_hint)`; 0.3 from the full store. This
///      keeps domain-relevant material front-and-centre while
///      preserving cross-domain leverage (a QM island still pulls
///      algebraic identities tagged `PureMath`).
///   3. Picked fragments are guaranteed to be sub-expressions of the
///      axiom statement: for an `Eq(LHS, RHS)` axiom we randomly pick
///      LHS or RHS; for non-`Eq` propositions (`Gt`, `Implies`, etc.)
///      we pick the LHS — these are sign-conditions / constraints
///      whose left-hand side is the meaningful fragment.
fn axiom_injection_with_store(
    expr: &Expr,
    store: Option<&AxiomStore>,
    domain_hint: Option<&nasrudin_core::Domain>,
    forbidden: &std::collections::HashSet<nasrudin_core::TheoremId>,
    rng: &mut impl Rng,
) -> Expr {
    if let Some(store) = store
        && store.len() > 0
        && let Some(fragment) = sample_axiom_fragment(store, domain_hint, forbidden, rng)
    {
        return replace_random_leaf(expr, &fragment, rng);
    }
    axiom_injection_legacy(expr, rng)
}

/// Sample a meaningful sub-expression from the AxiomStore. Returns
/// `None` if the store has no usable axioms for the domain.
///
/// **Cold-tier hot path:** `store.iter()` walks both hot and cold
/// tiers (~195 k entries). To keep the GA's per-mutation cost
/// bounded we route the "any axiom" branch through
/// [`AxiomStore::cold_names`] (a snapshot built once at boot) +
/// `store.get(name)` — O(1) name pick + one bloom-filtered RocksDB
/// fetch instead of a full O(N) iter walk per mutation. The
/// per-domain branch still calls `by_domain(d)` and chooses from
/// that bounded slice; for hot-only domains (SR, EM, classical)
/// this stays in-RAM.
fn sample_axiom_fragment(
    store: &AxiomStore,
    domain_hint: Option<&nasrudin_core::Domain>,
    forbidden: &std::collections::HashSet<nasrudin_core::TheoremId>,
    rng: &mut impl Rng,
) -> Option<Expr> {
    // 70/30 split: domain-matched preferred, full store fallback for
    // cross-domain leverage.
    let prefer_domain = domain_hint.is_some() && rng.random_bool(0.7);
    let chosen: Option<nasrudin_derive::Axiom> = if prefer_domain {
        let dom = domain_hint.unwrap();
        let domain_set = if forbidden.is_empty() {
            store.by_domain(dom)
        } else {
            store.by_domain_excluding(dom, forbidden)
        };
        if domain_set.is_empty() {
            sample_any_axiom(store, forbidden, rng)
        } else {
            domain_set.into_iter().choose(rng)
        }
    } else {
        sample_any_axiom(store, forbidden, rng)
    };
    let axiom = chosen?;
    Some(extract_meaningful_fragment(&axiom.statement, rng))
}

/// Pick a random axiom from the full store (hot ∪ cold) without
/// iterating the cold tier on every call. Two-stage:
///
/// 1. Flip a weighted coin between hot and cold based on tier sizes.
/// 2. Hot path: collect hot keys, choose one, look up.
/// 3. Cold path: index into the pre-snapshotted `cold_names` list,
///    look up via the bloom-filtered RocksDB CF.
///
/// Falls back gracefully when one tier is empty.
fn sample_any_axiom(
    store: &AxiomStore,
    forbidden: &std::collections::HashSet<nasrudin_core::TheoremId>,
    rng: &mut impl Rng,
) -> Option<nasrudin_derive::Axiom> {
    let cold_names = store.cold_names();
    let hot_keys: Vec<String> = store.iter_hot_names();
    let total = hot_keys.len() + cold_names.len();
    if total == 0 {
        return None;
    }
    // Up to 8 retries on a forbidden hit before giving up. With ~tens
    // of forbidden ids out of 195 k axioms, the probability of 8 hits
    // in a row is vanishing — we don't want a rare worst case where
    // every name we try is forbidden to spin forever.
    for _ in 0..8 {
        let pick = rng.random_range(0..total);
        let name = if pick < hot_keys.len() {
            &hot_keys[pick]
        } else {
            &cold_names[pick - hot_keys.len()]
        };
        if !forbidden.is_empty() && forbidden.contains(&nasrudin_core::axiom_id_from_name(name)) {
            continue;
        }
        return store.get(name);
    }
    None
}

/// Pick a meaningful sub-expression from a propositional axiom.
fn extract_meaningful_fragment(stmt: &Expr, rng: &mut impl Rng) -> Expr {
    match stmt {
        // For Eq(LHS, RHS) — both sides are useful. Pick at random.
        Expr::BinOp(BinOp::Eq | BinOp::Iff, l, r) => {
            if rng.random_bool(0.5) {
                (**l).clone()
            } else {
                (**r).clone()
            }
        }
        // For inequalities and implications, the LHS is usually the
        // structurally interesting fragment (a quantity being bounded
        // or an antecedent). RHS is often a literal (0, 1) or a
        // simple consequent.
        Expr::BinOp(
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Ne | BinOp::Implies,
            l,
            _,
        ) => (**l).clone(),
        // Pi-quantified — recurse into the body, which is the actual
        // proposition.
        Expr::Pi(_, _, body) => extract_meaningful_fragment(body, rng),
        // For And/Or — pick a conjunct/disjunct at random.
        Expr::BinOp(BinOp::And | BinOp::Or, l, r) => {
            if rng.random_bool(0.5) {
                (**l).clone()
            } else {
                (**r).clone()
            }
        }
        // Anything else — use the whole expression.
        other => other.clone(),
    }
}

/// Legacy 4-fragment hardcoded pool, preserved for back-compat with
/// callers that don't have an AxiomStore handy and as a fallback when
/// the store happens to be empty (e.g. early in worker boot).
fn axiom_injection_legacy(expr: &Expr, rng: &mut impl Rng) -> Expr {
    // Axiom fragments: common physics subexpressions
    let fragments = [
        // mc^2
        Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("m".into())),
            Box::new(Expr::BinOp(
                BinOp::Pow,
                Box::new(Expr::Const(PhysConst::SpeedOfLight)),
                Box::new(Expr::Lit(2, 1)),
            )),
        ),
        // hbar * omega
        Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Const(PhysConst::ReducedPlanck)),
            Box::new(Expr::Var("omega".into())),
        ),
        // k_B * T
        Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Const(PhysConst::Boltzmann)),
            Box::new(Expr::Var("T".into())),
        ),
        // p^2 / (2m)
        Expr::BinOp(
            BinOp::Div,
            Box::new(Expr::BinOp(
                BinOp::Pow,
                Box::new(Expr::Var("p".into())),
                Box::new(Expr::Lit(2, 1)),
            )),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Lit(2, 1)),
                Box::new(Expr::Var("m".into())),
            )),
        ),
    ];

    let fragment = &fragments[rng.random_range(0..fragments.len())];

    // Replace a random leaf node with the fragment
    replace_random_leaf(expr, fragment, rng)
}

/// Replace a random leaf in the expression with a replacement subtree.
fn replace_random_leaf(expr: &Expr, replacement: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::Var(_) | Expr::Const(_) | Expr::Lit(_, _) => {
            // This is a leaf; replace with some probability
            if rng.random_bool(0.3) {
                replacement.clone()
            } else {
                expr.clone()
            }
        }
        Expr::BinOp(op, l, r) => {
            if rng.random_bool(0.5) {
                Expr::BinOp(
                    op.clone(),
                    Box::new(replace_random_leaf(l, replacement, rng)),
                    r.clone(),
                )
            } else {
                Expr::BinOp(
                    op.clone(),
                    l.clone(),
                    Box::new(replace_random_leaf(r, replacement, rng)),
                )
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(
            op.clone(),
            Box::new(replace_random_leaf(e, replacement, rng)),
        ),
        other => other.clone(),
    }
}

/// Simplify: fold trivial constant subexpressions.
fn simplify(expr: &Expr) -> Expr {
    match expr {
        // x + 0 => x, 0 + x => x
        Expr::BinOp(BinOp::Add, l, r) => {
            if matches!(r.as_ref(), Expr::Lit(0, _)) {
                simplify(l)
            } else if matches!(l.as_ref(), Expr::Lit(0, _)) {
                simplify(r)
            } else {
                Expr::BinOp(BinOp::Add, Box::new(simplify(l)), Box::new(simplify(r)))
            }
        }
        // x * 1 => x, 1 * x => x
        Expr::BinOp(BinOp::Mul, l, r) => {
            if matches!(r.as_ref(), Expr::Lit(1, 1)) {
                simplify(l)
            } else if matches!(l.as_ref(), Expr::Lit(1, 1)) {
                simplify(r)
            } else if matches!(r.as_ref(), Expr::Lit(0, _)) || matches!(l.as_ref(), Expr::Lit(0, _))
            {
                Expr::Lit(0, 1)
            } else {
                Expr::BinOp(BinOp::Mul, Box::new(simplify(l)), Box::new(simplify(r)))
            }
        }
        // x ^ 1 => x, x ^ 0 => 1
        Expr::BinOp(BinOp::Pow, l, r) => {
            if matches!(r.as_ref(), Expr::Lit(1, 1)) {
                simplify(l)
            } else if matches!(r.as_ref(), Expr::Lit(0, _)) {
                Expr::Lit(1, 1)
            } else {
                Expr::BinOp(BinOp::Pow, Box::new(simplify(l)), Box::new(simplify(r)))
            }
        }
        // Double negation: --x => x
        Expr::UnOp(UnOp::Neg, inner) => {
            if let Expr::UnOp(UnOp::Neg, e) = inner.as_ref() {
                simplify(e)
            } else {
                Expr::UnOp(UnOp::Neg, Box::new(simplify(inner)))
            }
        }
        Expr::BinOp(op, l, r) => {
            Expr::BinOp(op.clone(), Box::new(simplify(l)), Box::new(simplify(r)))
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(simplify(e))),
        other => other.clone(),
    }
}

/// Unary operators suitable for wrapping.
const WRAP_OPS: &[UnOp] = &[UnOp::Neg, UnOp::Abs, UnOp::Sqrt, UnOp::Exp, UnOp::Ln];

/// Wrap a random subtree with a unary operator.
fn unary_wrap(expr: &Expr, rng: &mut impl Rng) -> Expr {
    let op = &WRAP_OPS[rng.random_range(0..WRAP_OPS.len())];
    // Wrap the whole expression with some probability, or recurse
    if rng.random_bool(0.4) {
        Expr::UnOp(op.clone(), Box::new(expr.clone()))
    } else {
        match expr {
            Expr::BinOp(bop, l, r) => {
                if rng.random_bool(0.5) {
                    Expr::BinOp(bop.clone(), Box::new(unary_wrap(l, rng)), r.clone())
                } else {
                    Expr::BinOp(bop.clone(), l.clone(), Box::new(unary_wrap(r, rng)))
                }
            }
            _ => Expr::UnOp(op.clone(), Box::new(expr.clone())),
        }
    }
}

/// Remove a unary operator, exposing its child directly.
fn unary_unwrap(expr: &Expr) -> Expr {
    match expr {
        Expr::UnOp(_, e) => *e.clone(),
        Expr::BinOp(op, l, r) => {
            // Try to unwrap in left or right child
            Expr::BinOp(
                op.clone(),
                Box::new(unary_unwrap(l)),
                Box::new(unary_unwrap(r)),
            )
        }
        other => other.clone(),
    }
}

/// Perturb a literal value by a small integer offset or ratio change.
fn lit_perturb(expr: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::Lit(n, d) => {
            let delta: i64 = rng.random_range(-2..=2);
            let new_n = n.saturating_add(delta);
            // Keep denominator positive
            let new_d = if *d == 0 { 1 } else { *d };
            Expr::Lit(new_n, new_d)
        }
        Expr::BinOp(op, l, r) => {
            if rng.random_bool(0.5) {
                Expr::BinOp(op.clone(), Box::new(lit_perturb(l, rng)), r.clone())
            } else {
                Expr::BinOp(op.clone(), l.clone(), Box::new(lit_perturb(r, rng)))
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(lit_perturb(e, rng))),
        other => other.clone(),
    }
}

/// All physical constants for swapping.
const ALL_CONSTS: &[PhysConst] = &[
    PhysConst::SpeedOfLight,
    PhysConst::PlanckConst,
    PhysConst::ReducedPlanck,
    PhysConst::GravConst,
    PhysConst::Boltzmann,
    PhysConst::ElectronCharge,
    PhysConst::ElectronMass,
    PhysConst::ProtonMass,
    PhysConst::Pi,
];

/// Swap a physical constant with a different one.
fn const_swap(expr: &Expr, rng: &mut impl Rng) -> Expr {
    match expr {
        Expr::Const(c) => {
            let new_const = loop {
                let candidate = &ALL_CONSTS[rng.random_range(0..ALL_CONSTS.len())];
                if candidate != c {
                    break candidate.clone();
                }
            };
            Expr::Const(new_const)
        }
        Expr::BinOp(op, l, r) => {
            if rng.random_bool(0.5) {
                Expr::BinOp(op.clone(), Box::new(const_swap(l, rng)), r.clone())
            } else {
                Expr::BinOp(op.clone(), l.clone(), Box::new(const_swap(r, rng)))
            }
        }
        Expr::UnOp(op, e) => Expr::UnOp(op.clone(), Box::new(const_swap(e, rng))),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simplify_add_zero() {
        let expr = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Lit(0, 1)),
        );
        let result = simplify(&expr);
        assert_eq!(result, Expr::Var("x".into()));
    }

    #[test]
    fn simplify_mul_one() {
        let expr = Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Lit(1, 1)),
            Box::new(Expr::Var("y".into())),
        );
        let result = simplify(&expr);
        assert_eq!(result, Expr::Var("y".into()));
    }

    #[test]
    fn simplify_pow_zero() {
        let expr = Expr::BinOp(
            BinOp::Pow,
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Lit(0, 1)),
        );
        let result = simplify(&expr);
        assert_eq!(result, Expr::Lit(1, 1));
    }

    #[test]
    fn mutate_produces_different_expr() {
        let expr = Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Var("m".into())),
            Box::new(Expr::Var("a".into())),
        );
        let mut rng = rand::rng();
        // Run mutation multiple times; at least one should differ
        let mut found_different = false;
        for _ in 0..20 {
            let mutated = mutate(&expr, &mut rng);
            if mutated != expr {
                found_different = true;
                break;
            }
        }
        assert!(
            found_different,
            "Mutation should produce different expressions"
        );
    }
}
