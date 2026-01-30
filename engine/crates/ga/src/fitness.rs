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

use nasrudin_core::{BinOp, Expr, FitnessScore, Theorem};
use nasrudin_derive::{check_equation_dimensions, sr_variable_dimensions};

/// Evaluate all 7 fitness objectives for a theorem candidate.
pub fn evaluate(theorem: &Theorem) -> FitnessScore {
    FitnessScore {
        novelty: novelty_score(theorem),
        complexity: complexity_score(&theorem.statement),
        depth: depth_score(theorem.depth),
        dimensional: dimensional_score(&theorem.statement),
        symmetry: symmetry_score(&theorem.statement),
        connectivity: connectivity_score(theorem),
        nasrudin_relevance: nasrudin_relevance_score(theorem),
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
/// Returns 1.0 if consistent, 0.0 if not (or unknown).
fn dimensional_score(expr: &Expr) -> f64 {
    let var_dims = sr_variable_dimensions();
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

/// Physics relevance: domain-specific heuristic.
/// Checks for presence of physical constants and meaningful structure.
fn nasrudin_relevance_score(theorem: &Theorem) -> f64 {
    let mut score: f64 = 0.0;

    // Has physical constants?
    if has_physical_constants(&theorem.statement) {
        score += 0.3;
    }

    // Is an equation (has Eq at root)?
    if matches!(&theorem.statement, Expr::BinOp(BinOp::Eq, _, _)) {
        score += 0.3;
    }

    // Has derivatives or integrals (dynamical content)?
    if has_calculus_ops(&theorem.statement) {
        score += 0.2;
    }

    // Uses multiple variables (not trivial)?
    let var_count = count_distinct_vars(&theorem.statement);
    if var_count >= 2 {
        score += 0.2;
    }

    score.min(1.0)
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
        // Has constants (0.3) + is equation (0.3) + multiple vars (0.2)
        assert!(fitness.nasrudin_relevance >= 0.7);
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
