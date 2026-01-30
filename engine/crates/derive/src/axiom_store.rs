//! Axiom registry for derivation.
//!
//! Stores named axioms (as `Expr` equations) organized by physics domain.
//! The derivation engine loads axioms relevant to its strategy.

use nasrudin_core::{BinOp, Domain, Expr, PhysConst};
use std::collections::HashMap;

/// A named axiom with its domain and expression.
#[derive(Debug, Clone)]
pub struct Axiom {
    /// Human-readable name (e.g., "energy_momentum_relation").
    pub name: String,
    /// The physics domain this axiom belongs to.
    pub domain: Domain,
    /// The axiom's mathematical statement as an expression.
    pub statement: Expr,
    /// Brief description.
    pub description: String,
}

/// Registry of axioms available for derivation.
#[derive(Debug, Clone, Default)]
pub struct AxiomStore {
    axioms: HashMap<String, Axiom>,
}

impl AxiomStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an axiom.
    pub fn register(&mut self, axiom: Axiom) {
        self.axioms.insert(axiom.name.clone(), axiom);
    }

    /// Look up an axiom by name.
    pub fn get(&self, name: &str) -> Option<&Axiom> {
        self.axioms.get(name)
    }

    /// Get all axioms in a given domain.
    pub fn by_domain(&self, domain: &Domain) -> Vec<&Axiom> {
        self.axioms.values().filter(|a| &a.domain == domain).collect()
    }

    /// Get all axiom names.
    pub fn names(&self) -> Vec<&str> {
        self.axioms.keys().map(|s| s.as_str()).collect()
    }

    /// Number of registered axioms.
    pub fn len(&self) -> usize {
        self.axioms.len()
    }

    pub fn is_empty(&self) -> bool {
        self.axioms.is_empty()
    }

    /// Load axioms from a PhysLean catalog JSON file.
    ///
    /// Parses the catalog and converts each theorem to an `Axiom` registered
    /// in the store. Returns the number of axioms loaded.
    ///
    /// This replaces the domain-specific `load_*()` methods.
    pub fn load_from_catalog(&mut self, catalog_path: &std::path::Path) -> anyhow::Result<usize> {
        let content = std::fs::read_to_string(catalog_path)?;
        let catalog: serde_json::Value = serde_json::from_str(&content)?;

        let mut count = 0;
        if let Some(theorems) = catalog.get("theorems").and_then(|t| t.as_array()) {
            for thm in theorems {
                let name = thm.get("name").and_then(|n| n.as_str()).unwrap_or("unknown");
                let domain_str = thm.get("domain").and_then(|d| d.as_str()).unwrap_or("PureMath");
                let doc = thm.get("doc_string")
                    .and_then(|d| d.as_str())
                    .unwrap_or("")
                    .to_string();

                let domain = match domain_str {
                    "ClassicalMechanics" => Domain::ClassicalMechanics,
                    "SpecialRelativity" => Domain::SpecialRelativity,
                    "Electromagnetism" => Domain::Electromagnetism,
                    "QuantumMechanics" => Domain::QuantumMechanics,
                    "Thermodynamics" => Domain::Thermodynamics,
                    "StatisticalMechanics" => Domain::StatisticalMechanics,
                    _ => Domain::PureMath,
                };

                // For catalog-loaded axioms, we store a placeholder Expr
                // since the type signatures are in Lean syntax, not our AST.
                // The GA engine will reference these by name.
                self.register(Axiom {
                    name: name.to_string(),
                    domain,
                    statement: Expr::Var(name.to_string()),
                    description: doc,
                });
                count += 1;
            }
        }

        tracing::info!("Loaded {count} axioms from catalog");
        Ok(count)
    }

    /// Load special relativity axioms (legacy — prefer `load_from_catalog`).
    ///
    /// Registers:
    /// - `mass_shell_condition`: E² − p²c² = (mc²)²  (definition)
    /// - `energy_nonneg`: E ≥ 0
    /// - `mass_nonneg`: m ≥ 0
    /// - `c_positive`: c > 0
    #[deprecated(note = "Use load_from_catalog() with the PhysLean catalog instead")]
    pub fn load_special_relativity(&mut self) {
        // Mass-shell condition: E² - p²c² = (mc²)²
        // As Expr: Eq(Sub(Pow(E,2), Mul(Pow(p,2), Pow(c,2))), Pow(Mul(m, Pow(c,2)), 2))
        let e = Expr::Var("E".into());
        let m = Expr::Var("m".into());
        let p = Expr::Var("p".into());
        let c = Expr::Const(PhysConst::SpeedOfLight);
        let two = Expr::Lit(2, 1);

        // E²
        let e_sq = Expr::BinOp(BinOp::Pow, Box::new(e.clone()), Box::new(two.clone()));
        // p²
        let p_sq = Expr::BinOp(BinOp::Pow, Box::new(p.clone()), Box::new(two.clone()));
        // c²
        let c_sq = Expr::BinOp(
            BinOp::Pow,
            Box::new(c.clone()),
            Box::new(two.clone()),
        );
        // p²c²
        let p_sq_c_sq = Expr::BinOp(BinOp::Mul, Box::new(p_sq), Box::new(c_sq.clone()));
        // mc²
        let mc_sq = Expr::BinOp(BinOp::Mul, Box::new(m.clone()), Box::new(c_sq.clone()));
        // (mc²)²
        let mc_sq_squared =
            Expr::BinOp(BinOp::Pow, Box::new(mc_sq.clone()), Box::new(two.clone()));
        // E² - p²c²
        let lhs = Expr::BinOp(BinOp::Sub, Box::new(e_sq), Box::new(p_sq_c_sq));
        // E² - p²c² = (mc²)²
        let mass_shell = Expr::BinOp(BinOp::Eq, Box::new(lhs), Box::new(mc_sq_squared));

        self.register(Axiom {
            name: "mass_shell_condition".into(),
            domain: Domain::SpecialRelativity,
            statement: mass_shell,
            description: "Mass-shell: E² − p²c² = (mc²)²".into(),
        });

        // E ≥ 0
        let e_nonneg = Expr::BinOp(
            BinOp::Ge,
            Box::new(e.clone()),
            Box::new(Expr::Lit(0, 1)),
        );
        self.register(Axiom {
            name: "energy_nonneg".into(),
            domain: Domain::SpecialRelativity,
            statement: e_nonneg,
            description: "Energy is non-negative".into(),
        });

        // m ≥ 0
        let m_nonneg = Expr::BinOp(
            BinOp::Ge,
            Box::new(m.clone()),
            Box::new(Expr::Lit(0, 1)),
        );
        self.register(Axiom {
            name: "mass_nonneg".into(),
            domain: Domain::SpecialRelativity,
            statement: m_nonneg,
            description: "Mass is non-negative".into(),
        });

        // c > 0
        let c_pos = Expr::BinOp(
            BinOp::Gt,
            Box::new(c.clone()),
            Box::new(Expr::Lit(0, 1)),
        );
        self.register(Axiom {
            name: "c_positive".into(),
            domain: Domain::SpecialRelativity,
            statement: c_pos,
            description: "Speed of light is positive".into(),
        });
    }
}
