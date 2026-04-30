//! 7-objective fitness evaluation for theorem candidates.
//!
//! Each objective produces a score in [0.0, 1.0]:
//! - novelty: how different from existing theorems
//! - complexity: preference for moderate complexity (not too simple, not too big)
//! - depth: derivation depth score
//! - dimensional: dimensional consistency (1.0 if consistent, 0.0 otherwise)
//! - symmetry: structural symmetry in the expression
//! - connectivity: how many known theorems this relates to
//! - nasrudin_relevance: domain-specific relevance signals

use nasrudin_core::{BinOp, Domain, Expr, FitnessScore, PhysConst, Theorem, UnOp};
use nasrudin_derive::{check_equation_dimensions, domain_variable_dimensions};

/// Evaluate all 7 fitness objectives for a theorem candidate.
pub fn evaluate(theorem: &Theorem) -> FitnessScore {
    evaluate_with_target(theorem, None)
}

/// Like [`evaluate`] but also score the candidate against an optional
/// `TargetSpec`. The target signals (`target_shape`, `ladder_progress`)
/// stay zero when no target is given — same behaviour as before.
pub fn evaluate_with_target(
    theorem: &Theorem,
    target: Option<&crate::target::TargetSpec>,
) -> FitnessScore {
    let (target_shape, ladder_progress) = match target {
        Some(spec) => (
            crate::target::shape_similarity(&theorem.statement, &spec.final_target),
            crate::target::ladder_score(&theorem.statement, spec),
        ),
        None => (0.0, 0.0),
    };
    FitnessScore {
        novelty: novelty_score(theorem),
        complexity: complexity_score(&theorem.statement),
        depth: depth_score(theorem.depth),
        dimensional: dimensional_score_for_domain(&theorem.statement, &theorem.domain),
        symmetry: symmetry_score(&theorem.statement),
        connectivity: connectivity_score(theorem),
        nasrudin_relevance: nasrudin_relevance_score(theorem),
        target_shape,
        ladder_progress,
    }
}

/// Novelty: based on canonical hash uniqueness.
/// Returns 1.0 for new theorems (real novelty checked against DB externally).
/// Here we use a heuristic based on expression variety.
fn novelty_score(theorem: &Theorem) -> f64 {
    // Count distinct variable names and constants as a proxy for novelty
    let canonical = &theorem.canonical;
    let unique_tokens: std::collections::HashSet<&str> = canonical
        .split(|c: char| !c.is_alphanumeric() && c != ':' && c != '_')
        .filter(|s| !s.is_empty())
        .collect();
    // More distinct symbols => potentially more novel
    let variety = unique_tokens.len() as f64;
    (variety / 15.0).min(1.0) // Normalize to [0, 1]
}

/// Complexity: prefer moderate complexity (Goldilocks zone).
/// Too simple (< 3 nodes) or too complex (> 30 nodes) gets penalized.
fn complexity_score(expr: &Expr) -> f64 {
    let n = expr.node_count() as f64;
    // Bell curve centered around 10-15 nodes
    let ideal = 12.0;
    let sigma = 8.0;
    let z = (n - ideal) / sigma;
    (-0.5 * z * z).exp()
}

/// Depth: prefer moderate derivation depth.
fn depth_score(depth: u32) -> f64 {
    let d = depth as f64;
    // Bell curve centered around depth 5-8
    let ideal = 6.0;
    let sigma = 4.0;
    let z = (d - ideal) / sigma;
    (-0.5 * z * z).exp()
}

/// Dimensional: check whether the expression is dimensionally consistent.
///
/// Uses the candidate theorem's *domain-aware* dimension table — a QM
/// expression is checked against QM variable dimensions, a thermo
/// expression against thermo dimensions, etc. Falls back to SR
/// dimensions for unrecognised domains. Returns 1.0 if consistent,
/// 0.0 if not (or unknown).
fn dimensional_score_for_domain(expr: &Expr, domain: &Domain) -> f64 {
    let var_dims = domain_variable_dimensions(domain);
    match check_equation_dimensions(expr, &var_dims) {
        Ok(_) => 1.0,
        Err(_) => 0.0,
    }
}

/// Symmetry: structural symmetry of the expression.
/// Measures whether left and right subtrees of binary ops are similar in size.
fn symmetry_score(expr: &Expr) -> f64 {
    match expr {
        Expr::BinOp(op, l, r) => {
            match op {
                BinOp::Eq | BinOp::Add | BinOp::Mul => {
                    let ln = l.node_count() as f64;
                    let rn = r.node_count() as f64;
                    let total = ln + rn;
                    if total == 0.0 {
                        return 1.0;
                    }
                    // Ratio of smaller to larger side
                    let ratio = ln.min(rn) / ln.max(rn);
                    // Blend with children's symmetry
                    let child_sym =
                        (symmetry_score(l) + symmetry_score(r)) / 2.0;
                    0.5 * ratio + 0.5 * child_sym
                }
                _ => {
                    // Non-commutative ops: just check children
                    (symmetry_score(l) + symmetry_score(r)) / 2.0
                }
            }
        }
        Expr::UnOp(_, e) => symmetry_score(e),
        // Leaves are perfectly symmetric
        _ => 1.0,
    }
}

/// Connectivity: how many parent theorems this is derived from.
fn connectivity_score(theorem: &Theorem) -> f64 {
    let parents = theorem.parents.len() as f64;
    // More parents = more connected to the theorem graph
    (parents / 5.0).min(1.0)
}

/// Physics relevance: domain-aware heuristic.
///
/// Layered scoring:
///   - Base layer (all domains): physical constants, equation root,
///     calculus, multiple variables — these are domain-agnostic
///     "physics-shapedness" signals.
///   - Domain-specific bonus: a QuantumMechanics theorem gets credit
///     for QM structural primitives (∂/∂t with ℏ → Schrödinger shape;
///     conjugation or `i_unit` → complex amplitude; tensor product →
///     state-space shape; integral of |·|² → normalization shape).
///     A Thermodynamics theorem gets credit for entropy-shape
///     signatures (S, T, k_B). Etc. These are *domain-aware* without
///     requiring any explicit `TargetSpec` — the system can score
///     spontaneous emergence of QM-shaped expressions higher even
///     when no QM target is configured.
fn nasrudin_relevance_score(theorem: &Theorem) -> f64 {
    let mut score: f64 = 0.0;

    // Has physical constants?
    if has_physical_constants(&theorem.statement) {
        score += 0.2;
    }

    // Is an equation (has Eq at root)?
    if matches!(&theorem.statement, Expr::BinOp(BinOp::Eq, _, _)) {
        score += 0.2;
    }

    // Has derivatives or integrals (dynamical content)?
    if has_calculus_ops(&theorem.statement) {
        score += 0.15;
    }

    // Uses multiple variables (not trivial)?
    let var_count = count_distinct_vars(&theorem.statement);
    if var_count >= 2 {
        score += 0.15;
    }

    // Domain-specific bonus (capped at 0.3 so base signals still
    // dominate when present).
    let dom_bonus = domain_specific_signal(&theorem.statement, &theorem.domain);
    score += dom_bonus.min(0.3);

    score.min(1.0)
}

/// Domain-specific structural signal in `[0, 0.5]`.
///
/// Recognises shapes the system should reward as "this looks like the
/// kind of theorem this domain produces", *without* requiring a
/// `TargetSpec`. The point is that a randomly-evolved expression that
/// happens to look like a Schrödinger equation gets fitness credit
/// even when no human has pointed the GA at a target.
fn domain_specific_signal(expr: &Expr, domain: &Domain) -> f64 {
    match domain {
        Domain::QuantumMechanics => quantum_signal(expr),
        Domain::Thermodynamics | Domain::StatisticalMechanics => thermal_signal(expr),
        Domain::GeneralRelativity => gr_signal(expr),
        _ => 0.0,
    }
}

fn quantum_signal(expr: &Expr) -> f64 {
    let mut s = 0.0_f64;
    // Schrödinger shape: ∂/∂t somewhere AND ℏ (ReducedPlanck) somewhere.
    if has_partial_deriv_var(expr, "t") && contains_const(expr, &PhysConst::ReducedPlanck) {
        s += 0.20;
    }
    // Complex-amplitude shape: conjugation (Â† or ψ*) or imaginary unit.
    if has_unop(expr, &UnOp::Conjugate) || contains_var(expr, "i_unit") {
        s += 0.10;
    }
    // State-space shape: tensor product, dot product (inner product).
    if has_binop(expr, &BinOp::TensorProduct) || has_binop(expr, &BinOp::Dot) {
        s += 0.10;
    }
    // Normalization shape: integral of squared-abs over x.
    if has_normalization_shape(expr) {
        s += 0.10;
    }
    // Operator-acting-on-state shape: App with name ending in _op.
    if has_operator_application(expr) {
        s += 0.05;
    }
    s
}

fn thermal_signal(expr: &Expr) -> f64 {
    let mut s = 0.0_f64;
    // Boltzmann-related: ln, k_B, exp.
    if has_unop(expr, &UnOp::Ln) || contains_const(expr, &PhysConst::Boltzmann) {
        s += 0.10;
    }
    if has_unop(expr, &UnOp::Exp) {
        s += 0.10;
    }
    // T appearing as a variable (temperature).
    if contains_var(expr, "T") {
        s += 0.05;
    }
    // Entropy shape: S = ... or partition-function-like.
    if contains_var(expr, "S") || contains_var(expr, "Z") {
        s += 0.05;
    }
    s
}

fn gr_signal(expr: &Expr) -> f64 {
    let mut s = 0.0_f64;
    // Curvature/metric tensor slot vars.
    for v in ["g_metric", "R_ricci", "R_scalar", "T_stress"] {
        if contains_var(expr, v) {
            s += 0.10;
            break;
        }
    }
    // Newton's constant or speed of light squared.
    if contains_const(expr, &PhysConst::GravConst) {
        s += 0.10;
    }
    if has_pow_const(expr, &PhysConst::SpeedOfLight, 4) {
        s += 0.05;
    }
    s
}

// ---- structural predicates ----

fn contains_var(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Var(n) => n.as_str() == name,
        Expr::BinOp(_, l, r) => contains_var(l, name) || contains_var(r, name),
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => contains_var(e, name),
        Expr::App(f, x) => contains_var(f, name) || contains_var(x, name),
        Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) | Expr::Let(_, ty, body) => {
            contains_var(ty, name) || contains_var(body, name)
        }
        Expr::Integral { body, lower, upper, .. } => {
            contains_var(body, name)
                || lower.as_ref().is_some_and(|l| contains_var(l, name))
                || upper.as_ref().is_some_and(|u| contains_var(u, name))
        }
        Expr::Sum { body, lower, upper, .. } | Expr::Prod { body, lower, upper, .. } => {
            contains_var(body, name) || contains_var(lower, name) || contains_var(upper, name)
        }
        Expr::Limit { body, approaching, .. } => {
            contains_var(body, name) || contains_var(approaching, name)
        }
        _ => false,
    }
}

fn contains_const(expr: &Expr, c: &PhysConst) -> bool {
    match expr {
        Expr::Const(k) => k == c,
        Expr::BinOp(_, l, r) => contains_const(l, c) || contains_const(r, c),
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => contains_const(e, c),
        Expr::App(f, x) => contains_const(f, c) || contains_const(x, c),
        Expr::Integral { body, lower, upper, .. } => {
            contains_const(body, c)
                || lower.as_ref().is_some_and(|l| contains_const(l, c))
                || upper.as_ref().is_some_and(|u| contains_const(u, c))
        }
        Expr::Sum { body, lower, upper, .. } | Expr::Prod { body, lower, upper, .. } => {
            contains_const(body, c) || contains_const(lower, c) || contains_const(upper, c)
        }
        _ => false,
    }
}

fn has_partial_deriv_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::PartialDeriv(inner, v) => v.as_str() == var || has_partial_deriv_var(inner, var),
        Expr::BinOp(_, l, r) => has_partial_deriv_var(l, var) || has_partial_deriv_var(r, var),
        Expr::UnOp(_, e) | Expr::Deriv(e, _) => has_partial_deriv_var(e, var),
        Expr::App(f, x) => has_partial_deriv_var(f, var) || has_partial_deriv_var(x, var),
        Expr::Integral { body, .. } => has_partial_deriv_var(body, var),
        _ => false,
    }
}

fn has_unop(expr: &Expr, op: &UnOp) -> bool {
    match expr {
        Expr::UnOp(o, e) => o == op || has_unop(e, op),
        Expr::BinOp(_, l, r) => has_unop(l, op) || has_unop(r, op),
        Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => has_unop(e, op),
        Expr::App(f, x) => has_unop(f, op) || has_unop(x, op),
        Expr::Integral { body, .. } => has_unop(body, op),
        _ => false,
    }
}

fn has_binop(expr: &Expr, op: &BinOp) -> bool {
    match expr {
        Expr::BinOp(o, l, r) => o == op || has_binop(l, op) || has_binop(r, op),
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => has_binop(e, op),
        Expr::App(f, x) => has_binop(f, op) || has_binop(x, op),
        Expr::Integral { body, .. } => has_binop(body, op),
        _ => false,
    }
}

/// Recognise the normalization shape: ∫ Pow(Abs(_), 2) [d_].
fn has_normalization_shape(expr: &Expr) -> bool {
    match expr {
        Expr::Integral { body, .. } => is_abs_squared(body),
        Expr::BinOp(_, l, r) => has_normalization_shape(l) || has_normalization_shape(r),
        Expr::UnOp(_, e) => has_normalization_shape(e),
        _ => false,
    }
}

fn is_abs_squared(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::BinOp(BinOp::Pow, lhs, rhs)
            if matches!(lhs.as_ref(), Expr::UnOp(UnOp::Abs, _))
                && matches!(rhs.as_ref(), Expr::Lit(2, 1))
    )
}

/// Recognise an operator-application shape: App(Var, Var) where the
/// applied head's name ends with `_op`.
fn has_operator_application(expr: &Expr) -> bool {
    match expr {
        Expr::App(f, _) => matches!(f.as_ref(), Expr::Var(n) if n.ends_with("_op")),
        Expr::BinOp(_, l, r) => has_operator_application(l) || has_operator_application(r),
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => {
            has_operator_application(e)
        }
        _ => false,
    }
}

/// Recognise `Pow(Const(c), Lit(n, 1))` — useful for "c^4" in EFE.
fn has_pow_const(expr: &Expr, c: &PhysConst, n: i64) -> bool {
    match expr {
        Expr::BinOp(BinOp::Pow, base, exp) => {
            let base_match = matches!(base.as_ref(), Expr::Const(k) if k == c);
            let exp_match = matches!(exp.as_ref(), Expr::Lit(m, 1) if *m == n);
            (base_match && exp_match)
                || has_pow_const(base, c, n)
                || has_pow_const(exp, c, n)
        }
        Expr::BinOp(_, l, r) => has_pow_const(l, c, n) || has_pow_const(r, c, n),
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => has_pow_const(e, c, n),
        Expr::App(f, x) => has_pow_const(f, c, n) || has_pow_const(x, c, n),
        _ => false,
    }
}

/// Check if an expression contains any physical constants.
fn has_physical_constants(expr: &Expr) -> bool {
    match expr {
        Expr::Const(_) => true,
        Expr::BinOp(_, l, r) => has_physical_constants(l) || has_physical_constants(r),
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => {
            has_physical_constants(e)
        }
        Expr::App(f, x) => has_physical_constants(f) || has_physical_constants(x),
        Expr::Integral { body, .. } => has_physical_constants(body),
        _ => false,
    }
}

/// Check if an expression contains derivatives or integrals.
fn has_calculus_ops(expr: &Expr) -> bool {
    match expr {
        Expr::Deriv(_, _) | Expr::PartialDeriv(_, _) | Expr::Integral { .. } => true,
        Expr::BinOp(_, l, r) => has_calculus_ops(l) || has_calculus_ops(r),
        Expr::UnOp(_, e) => has_calculus_ops(e),
        Expr::App(f, x) => has_calculus_ops(f) || has_calculus_ops(x),
        _ => false,
    }
}

/// Count distinct variable names in an expression.
fn count_distinct_vars(expr: &Expr) -> usize {
    let mut vars = std::collections::HashSet::new();
    collect_vars(expr, &mut vars);
    vars.len()
}

fn collect_vars(expr: &Expr, vars: &mut std::collections::HashSet<String>) {
    match expr {
        Expr::Var(name) => {
            vars.insert(name.clone());
        }
        Expr::BinOp(_, l, r) => {
            collect_vars(l, vars);
            collect_vars(r, vars);
        }
        Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => {
            collect_vars(e, vars);
        }
        Expr::App(f, x) => {
            collect_vars(f, vars);
            collect_vars(x, vars);
        }
        Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) | Expr::Let(_, ty, body) => {
            collect_vars(ty, vars);
            collect_vars(body, vars);
        }
        Expr::Integral { body, lower, upper, .. } => {
            collect_vars(body, vars);
            if let Some(l) = lower {
                collect_vars(l, vars);
            }
            if let Some(u) = upper {
                collect_vars(u, vars);
            }
        }
        Expr::Sum { body, lower, upper, .. } => {
            collect_vars(body, vars);
            collect_vars(lower, vars);
            collect_vars(upper, vars);
        }
        Expr::Limit { body, approaching, .. } => {
            collect_vars(body, vars);
            collect_vars(approaching, vars);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nasrudin_core::{Domain, PhysConst, ProofTree, TheoremOrigin, VerificationStatus};

    fn make_test_theorem(statement: Expr) -> Theorem {
        let canonical = statement.to_canonical();
        let id = nasrudin_core::compute_theorem_id(&canonical);
        Theorem {
            id,
            statement,
            canonical,
            latex: String::new(),
            proof: ProofTree::Axiom([0; 8]),
            depth: 3,
            complexity: 5,
            domain: Domain::SpecialRelativity,
            dimension: None,
            parents: vec![],
            children: vec![],
            verified: VerificationStatus::Pending,
            fitness: FitnessScore::default(),
            generation: 0,
            created_at: 0,
            origin: TheoremOrigin::Axiom,
        }
    }

    #[test]
    fn dimensional_consistency_scores_high() {
        // E = mc^2 is dimensionally consistent
        let emc2 = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("E".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Var("m".into())),
                Box::new(Expr::BinOp(
                    BinOp::Pow,
                    Box::new(Expr::Const(PhysConst::SpeedOfLight)),
                    Box::new(Expr::Lit(2, 1)),
                )),
            )),
        );
        let thm = make_test_theorem(emc2);
        let fitness = evaluate(&thm);
        assert_eq!(fitness.dimensional, 1.0);
    }

    #[test]
    fn nasrudin_relevance_with_constants() {
        let expr = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("E".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Const(PhysConst::ReducedPlanck)),
                Box::new(Expr::Var("omega".into())),
            )),
        );
        let thm = make_test_theorem(expr);
        let fitness = evaluate(&thm);
        // Re-weighted in domain-aware fitness:
        //   constants 0.2 + equation 0.2 + multiple vars 0.15
        //   (no calculus ops, SR domain → no domain bonus) = 0.55.
        assert!(
            fitness.nasrudin_relevance >= 0.5,
            "expected ≥0.5 for E=ℏω, got {}",
            fitness.nasrudin_relevance
        );
    }

    #[test]
    fn nasrudin_relevance_qm_schrodinger_shape() {
        // A canonical Schrödinger-like expression should score higher
        // on the QM domain than the same shape on a non-QM domain,
        // confirming the domain-specific signal is wired.
        use nasrudin_core::UnOp;
        // iℏ ∂ψ/∂t = Ĥ·ψ  (encoded against the QM postulate convention)
        let psi = Expr::Var("psi".into());
        let i_unit = Expr::Var("i_unit".into());
        let hbar = Expr::Const(PhysConst::ReducedPlanck);
        let h_op = Expr::Var("H_op".into());
        let dpsi_dt = Expr::PartialDeriv(Box::new(psi.clone()), "t".into());
        let lhs = Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::BinOp(BinOp::Mul, Box::new(i_unit), Box::new(hbar))),
            Box::new(dpsi_dt),
        );
        let rhs = Expr::App(Box::new(h_op), Box::new(psi));
        let stmt = Expr::BinOp(BinOp::Eq, Box::new(lhs), Box::new(rhs));

        let mut thm_qm = make_test_theorem(stmt.clone());
        thm_qm.domain = Domain::QuantumMechanics;
        let thm_sr = make_test_theorem(stmt);
        // already SR via make_test_theorem default

        let f_qm = evaluate(&thm_qm);
        let f_sr = evaluate(&thm_sr);
        assert!(
            f_qm.nasrudin_relevance > f_sr.nasrudin_relevance,
            "QM-shaped expr should score higher on QM domain ({}) than SR ({})",
            f_qm.nasrudin_relevance,
            f_sr.nasrudin_relevance
        );
        assert!(
            f_qm.nasrudin_relevance >= 0.6,
            "QM-shaped Schrödinger should score ≥0.6, got {}",
            f_qm.nasrudin_relevance
        );
        // suppress unused — Domain is needed by the assertion above
        let _ = UnOp::Conjugate;
    }

    #[test]
    fn complexity_score_moderate() {
        // Moderate complexity expression (~7 nodes)
        let expr = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("F".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Var("m".into())),
                Box::new(Expr::Var("a".into())),
            )),
        );
        let score = complexity_score(&expr);
        assert!(score > 0.5, "Moderate complexity should score well: {score}");
    }
}
