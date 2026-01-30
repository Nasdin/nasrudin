//! Derivation context: tracks known facts, assumptions, and proof steps.

use nasrudin_core::Expr;

/// A single step in a derivation.
#[derive(Debug, Clone)]
pub struct DerivationStep {
    /// Human-readable description of what this step does.
    pub description: String,
    /// The rule or operation applied.
    pub rule: String,
    /// The resulting expression after this step.
    pub result: Expr,
}

/// Tracks the state of an ongoing derivation.
#[derive(Debug, Clone)]
pub struct DerivationContext {
    /// Named facts available (axioms + derived).
    known_facts: Vec<(String, Expr)>,
    /// Current assumptions (e.g., p = 0).
    assumptions: Vec<(String, Expr)>,
    /// Ordered derivation steps.
    steps: Vec<DerivationStep>,
    /// The current working expression.
    current: Option<Expr>,
}

impl DerivationContext {
    pub fn new() -> Self {
        Self {
            known_facts: Vec::new(),
            assumptions: Vec::new(),
            steps: Vec::new(),
            current: None,
        }
    }

    /// Add a known fact (axiom or previously derived).
    pub fn add_fact(&mut self, name: impl Into<String>, expr: Expr) {
        self.known_facts.push((name.into(), expr));
    }

    /// Add an assumption to the context.
    pub fn assume(&mut self, name: impl Into<String>, expr: Expr) {
        self.assumptions.push((name.into(), expr));
    }

    /// Record a derivation step and update the current expression.
    pub fn record_step(&mut self, description: impl Into<String>, rule: impl Into<String>, result: Expr) {
        let step = DerivationStep {
            description: description.into(),
            rule: rule.into(),
            result: result.clone(),
        };
        self.steps.push(step);
        self.current = Some(result);
    }

    /// Get the current working expression.
    pub fn current(&self) -> Option<&Expr> {
        self.current.as_ref()
    }

    /// Set the current working expression.
    pub fn set_current(&mut self, expr: Expr) {
        self.current = Some(expr);
    }

    /// Get all derivation steps.
    pub fn steps(&self) -> &[DerivationStep] {
        &self.steps
    }

    /// Get known facts.
    pub fn facts(&self) -> &[(String, Expr)] {
        &self.known_facts
    }

    /// Get assumptions.
    pub fn assumptions(&self) -> &[(String, Expr)] {
        &self.assumptions
    }

    /// Look up a fact by name.
    pub fn get_fact(&self, name: &str) -> Option<&Expr> {
        self.known_facts
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, e)| e)
    }
}

impl Default for DerivationContext {
    fn default() -> Self {
        Self::new()
    }
}
