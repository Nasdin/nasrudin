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

    /// Iterate over all registered axioms in unspecified order.
    ///
    /// Used by `/api/seed` to expose the full catalog to remote workers.
    pub fn iter(&self) -> impl Iterator<Item = &Axiom> {
        self.axioms.values()
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
        let mut ast_count = 0;
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

                // Prefer the structured `expr_ast` field (emitted by the
                // updated PhysLean extractor); fall back to a `Var`
                // placeholder when the entry is decorative-only. The GA
                // can compose meaningfully only with real Expr trees;
                // placeholder entries stay introducible by name but
                // can't participate in `RearrangeEquation` etc.
                let statement = thm
                    .get("expr_ast")
                    .filter(|v| !v.is_null())
                    .and_then(|v| serde_json::from_value::<Expr>(v.clone()).ok())
                    .map(|e| {
                        ast_count += 1;
                        e
                    })
                    .unwrap_or_else(|| Expr::Var(name.to_string()));

                self.register(Axiom {
                    name: name.to_string(),
                    domain,
                    statement,
                    description: doc,
                });
                count += 1;
            }
        }

        tracing::info!(
            "Loaded {count} axioms from catalog ({ast_count} with structured Expr AST, {} placeholder)",
            count - ast_count
        );
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

    /// Load **truly upstream** SR axioms suitable for spontaneous E=mc²
    /// derivation.
    ///
    /// The forbidden `mass_shell_condition` (which contains `m·c²` as a
    /// sub-expression and pre-supposes E=mc²) is **not** registered here.
    /// Instead, this loads the more fundamental definitions of
    /// four-momentum components and the Minkowski invariant. From these,
    /// the mass-shell condition becomes a *derivable* theorem.
    ///
    /// Encoding choice: four-momentum is represented as 4 scalar
    /// components (`p0`, `p1`, `p2`, `p3`) with `psq` standing for the
    /// squared 3-momentum magnitude `p1²+p2²+p3²` and `Msq` standing for
    /// the Minkowski invariant `p0²−psq`. Lean term `c` resolves to the
    /// PhysicsGenerator constant.
    ///
    /// Registers:
    /// - `four_momentum_time_component`:  `c · p0 = E`
    ///   (definition: energy is c × the time component of four-momentum)
    /// - `minkowski_invariant_def`:       `Msq = p0² − psq`
    ///   (definition of the Lorentz-invariant inner-product squared)
    /// - `invariant_mass_postulate`:      `Msq = m² · c²`
    ///   (postulate: the geometric invariant equals m²c² — the *physics*)
    /// - `rest_frame_psq_zero`:           `psq = 0`
    ///   (rest frame existence + spatial-momentum-squared vanishes)
    /// - `c_positive`, `mass_nonneg`, `energy_nonneg`: sign conditions
    ///
    /// Note that `psq = p1²+p2²+p3²` is *not* registered as a separate
    /// axiom; it is folded into `rest_frame_psq_zero` directly. A future
    /// version could add this as a separate definition once the
    /// derivation engine supports it.
    pub fn load_special_relativity_upstream(&mut self) {
        let e = Expr::Var("E".into());
        let m = Expr::Var("m".into());
        let c = Expr::Const(PhysConst::SpeedOfLight);
        let two = Expr::Lit(2, 1);
        let zero = Expr::Lit(0, 1);
        let p0 = Expr::Var("p0".into());
        let psq = Expr::Var("psq".into());
        let big_m_sq = Expr::Var("Msq".into());

        // c · p0 = E
        let four_mom_time = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::BinOp(BinOp::Mul, Box::new(c.clone()), Box::new(p0.clone()))),
            Box::new(e.clone()),
        );
        self.register(Axiom {
            name: "four_momentum_time_component".into(),
            domain: Domain::SpecialRelativity,
            statement: four_mom_time,
            description: "Definition: c · p0 = E (energy is c times the time component of four-momentum)".into(),
        });

        // Msq = p0² − psq
        let p0_sq = Expr::BinOp(BinOp::Pow, Box::new(p0.clone()), Box::new(two.clone()));
        let invariant_def = Expr::BinOp(
            BinOp::Eq,
            Box::new(big_m_sq.clone()),
            Box::new(Expr::BinOp(BinOp::Sub, Box::new(p0_sq), Box::new(psq.clone()))),
        );
        self.register(Axiom {
            name: "minkowski_invariant_def".into(),
            domain: Domain::SpecialRelativity,
            statement: invariant_def,
            description: "Definition: Msq = p0² − psq (Minkowski invariant of four-momentum)".into(),
        });

        // Msq = m² · c²
        let m_sq = Expr::BinOp(BinOp::Pow, Box::new(m.clone()), Box::new(two.clone()));
        let c_sq = Expr::BinOp(BinOp::Pow, Box::new(c.clone()), Box::new(two.clone()));
        let m_sq_c_sq = Expr::BinOp(BinOp::Mul, Box::new(m_sq), Box::new(c_sq));
        let mass_postulate = Expr::BinOp(
            BinOp::Eq,
            Box::new(big_m_sq.clone()),
            Box::new(m_sq_c_sq),
        );
        self.register(Axiom {
            name: "invariant_mass_postulate".into(),
            domain: Domain::SpecialRelativity,
            statement: mass_postulate,
            description: "Postulate: Msq = m²·c² (the Minkowski invariant equals invariant rest mass squared times c²)".into(),
        });

        // psq = 0 (rest frame)
        let rest = Expr::BinOp(BinOp::Eq, Box::new(psq.clone()), Box::new(zero));
        self.register(Axiom {
            name: "rest_frame_psq_zero".into(),
            domain: Domain::SpecialRelativity,
            statement: rest,
            description: "Rest-frame existence: in some inertial frame the spatial-momentum magnitude squared vanishes (psq = 0)".into(),
        });

        // Sign conditions.
        let c_pos = Expr::BinOp(BinOp::Gt, Box::new(c.clone()), Box::new(Expr::Lit(0, 1)));
        self.register(Axiom {
            name: "c_positive".into(),
            domain: Domain::SpecialRelativity,
            statement: c_pos,
            description: "Speed of light is positive".into(),
        });
        let m_nn = Expr::BinOp(BinOp::Ge, Box::new(m.clone()), Box::new(Expr::Lit(0, 1)));
        self.register(Axiom {
            name: "mass_nonneg".into(),
            domain: Domain::SpecialRelativity,
            statement: m_nn,
            description: "Mass is non-negative".into(),
        });
        let e_nn = Expr::BinOp(BinOp::Ge, Box::new(e.clone()), Box::new(Expr::Lit(0, 1)));
        self.register(Axiom {
            name: "energy_nonneg".into(),
            domain: Domain::SpecialRelativity,
            statement: e_nn,
            description: "Energy is non-negative".into(),
        });
    }

    /// Load **truly upstream** electromagnetism axioms suitable for
    /// spontaneous derivation of photon and wave-energy theorems.
    ///
    /// The headline EM result we want to derive is the photon
    /// energy-momentum relation `E_photon = c · p_photon`. To not
    /// cheat, we don't axiomatise that directly; instead we register
    /// the underlying postulates from which it follows:
    ///
    /// - `photon_energy_def`:    `Eph = hbar · omega`  (Planck-Einstein)
    /// - `photon_momentum_def`:  `pph = hbar · k`      (de Broglie)
    /// - `dispersion_relation`:  `omega = c · k`        (massless wave)
    /// - sign conditions: `c > 0`, `hbar > 0`
    ///
    /// From these, the GA / `linarith` chain produces:
    /// `Eph = hbar · omega = hbar · (c · k) = c · (hbar · k) = c · pph`.
    ///
    /// Note: `Eph`, `pph`, `omega`, `k`, `hbar` are scalar Expr Vars.
    pub fn load_electromagnetism_upstream(&mut self) {
        let e_ph = Expr::Var("Eph".into());
        let p_ph = Expr::Var("pph".into());
        let omega = Expr::Var("omega".into());
        let k = Expr::Var("k".into());
        let hbar = Expr::Var("hbar".into());
        let c = Expr::Const(PhysConst::SpeedOfLight);

        // Eph = hbar * omega
        let photon_energy = Expr::BinOp(
            BinOp::Eq,
            Box::new(e_ph.clone()),
            Box::new(Expr::BinOp(BinOp::Mul, Box::new(hbar.clone()), Box::new(omega.clone()))),
        );
        self.register(Axiom {
            name: "photon_energy_def".into(),
            domain: Domain::Electromagnetism,
            statement: photon_energy,
            description: "Planck-Einstein: Eph = ℏ · ω".into(),
        });

        // pph = hbar * k
        let photon_momentum = Expr::BinOp(
            BinOp::Eq,
            Box::new(p_ph.clone()),
            Box::new(Expr::BinOp(BinOp::Mul, Box::new(hbar.clone()), Box::new(k.clone()))),
        );
        self.register(Axiom {
            name: "photon_momentum_def".into(),
            domain: Domain::Electromagnetism,
            statement: photon_momentum,
            description: "de Broglie momentum: pph = ℏ · k".into(),
        });

        // omega = c * k
        let dispersion = Expr::BinOp(
            BinOp::Eq,
            Box::new(omega.clone()),
            Box::new(Expr::BinOp(BinOp::Mul, Box::new(c.clone()), Box::new(k.clone()))),
        );
        self.register(Axiom {
            name: "dispersion_relation".into(),
            domain: Domain::Electromagnetism,
            statement: dispersion,
            description: "Massless wave dispersion: ω = c · k".into(),
        });

        // c > 0
        let c_pos = Expr::BinOp(BinOp::Gt, Box::new(c.clone()), Box::new(Expr::Lit(0, 1)));
        self.register(Axiom {
            name: "c_positive_em".into(),
            domain: Domain::Electromagnetism,
            statement: c_pos,
            description: "Speed of light positive (EM)".into(),
        });

        // hbar > 0
        let hbar_pos = Expr::BinOp(BinOp::Gt, Box::new(hbar.clone()), Box::new(Expr::Lit(0, 1)));
        self.register(Axiom {
            name: "hbar_positive".into(),
            domain: Domain::Electromagnetism,
            statement: hbar_pos,
            description: "Reduced Planck constant positive".into(),
        });
    }
}
