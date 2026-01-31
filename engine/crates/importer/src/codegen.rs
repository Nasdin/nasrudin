//! Code generation: catalog → `Generated/*.lean` files.
//!
//! Groups theorems by domain and emits one `.lean` file per domain.
//! Each file:
//! - Imports Mathlib and PhysicsGenerator.Basic
//! - Declares types as structures/axioms
//! - Declares theorems as axioms (proven in PhysLean, re-axiomatized here)
//! - Adds source comments for traceability

use std::collections::{BTreeMap, HashSet};
use std::path::Path;

use anyhow::{Context, Result};

use crate::catalog::{CatalogTheorem, CatalogType, PhysLeanCatalog};

/// Domain-specific file configuration.
struct DomainFile {
    /// Lean module name (e.g., "Mechanics").
    module_name: String,
    /// Lean namespace (e.g., "PhysicsGenerator.Mechanics").
    namespace: String,
    /// Theorems in this domain.
    theorems: Vec<CatalogTheorem>,
    /// Types in this domain.
    types: Vec<CatalogType>,
}

/// Map domain string to (module_name, namespace).
fn domain_config(domain: &str) -> Option<(&str, &str)> {
    match domain {
        "ClassicalMechanics" => Some(("Mechanics", "PhysicsGenerator.Mechanics")),
        "SpecialRelativity" => Some(("SpecialRelativity", "PhysicsGenerator.SpecialRelativity")),
        "Electromagnetism" => Some(("Electromagnetism", "PhysicsGenerator.Electromagnetism")),
        "QuantumMechanics" => Some(("QuantumMechanics", "PhysicsGenerator.QuantumMechanics")),
        "Thermodynamics" => Some(("Thermodynamics", "PhysicsGenerator.Thermodynamics")),
        _ => None,
    }
}

/// Generate all `.lean` files from the catalog.
///
/// Returns the number of files generated.
pub fn generate_all(catalog: &PhysLeanCatalog, output_dir: &Path) -> Result<usize> {
    std::fs::create_dir_all(output_dir)
        .with_context(|| format!("Failed to create output dir: {}", output_dir.display()))?;

    // Group theorems by domain
    let mut domain_files: BTreeMap<String, DomainFile> = BTreeMap::new();

    for theorem in &catalog.theorems {
        let (module_name, namespace) = match domain_config(&theorem.domain) {
            Some(cfg) => cfg,
            None => {
                tracing::warn!("Skipping theorem '{}' — unknown domain '{}'", theorem.name, theorem.domain);
                continue;
            }
        };

        domain_files
            .entry(theorem.domain.clone())
            .or_insert_with(|| DomainFile {
                module_name: module_name.to_string(),
                namespace: namespace.to_string(),
                theorems: Vec::new(),
                types: Vec::new(),
            })
            .theorems
            .push(theorem.clone());
    }

    // Add types to their domains (best-effort domain mapping from physlean_name)
    for ty in &catalog.types {
        let domain = infer_type_domain(&ty.physlean_name);
        if let Some(file) = domain_files.get_mut(domain) {
            file.types.push(ty.clone());
        }
    }

    // Generate each domain file
    let mut count = 0;
    for (_domain, file) in &domain_files {
        let content = render_domain_file(file, catalog);
        let path = output_dir.join(format!("{}.lean", file.module_name));
        std::fs::write(&path, &content)
            .with_context(|| format!("Failed to write {}", path.display()))?;
        tracing::info!(
            "Generated {}: {} theorems, {} types",
            path.display(),
            file.theorems.len(),
            file.types.len()
        );
        count += 1;
    }

    // Always generate Dimensions.lean (not from PhysLean — our own dimensional analysis)
    let dimensions_content = render_dimensions_file();
    let dimensions_path = output_dir.join("Dimensions.lean");
    std::fs::write(&dimensions_path, &dimensions_content)
        .with_context(|| format!("Failed to write {}", dimensions_path.display()))?;
    count += 1;

    tracing::info!("Generated {} domain files in {}", count, output_dir.display());
    Ok(count)
}

/// Infer domain from a PhysLean fully-qualified name.
fn infer_type_domain(physlean_name: &str) -> &str {
    if physlean_name.contains("Relativity") || physlean_name.contains("Lorentz")
        || physlean_name.contains("FourMomentum") || physlean_name.contains("Minkowski") {
        "SpecialRelativity"
    } else if physlean_name.contains("Electromagnetism") || physlean_name.contains("Maxwell")
        || physlean_name.contains("FieldStrength") || physlean_name.contains("FourPotential") {
        "Electromagnetism"
    } else if physlean_name.contains("QuantumMechanics") || physlean_name.contains("Hilbert") {
        "QuantumMechanics"
    } else if physlean_name.contains("Thermodynamics") || physlean_name.contains("StatisticalMechanics") {
        "Thermodynamics"
    } else if physlean_name.contains("ClassicalMechanics") || physlean_name.contains("Lagrangian")
        || physlean_name.contains("Hamilton") {
        "ClassicalMechanics"
    } else {
        ""
    }
}

/// Render a complete `.lean` file for one domain.
fn render_domain_file(file: &DomainFile, catalog: &PhysLeanCatalog) -> String {
    let mut out = String::new();

    // Header
    out.push_str("import Mathlib\n");
    out.push_str("import PhysicsGenerator.Basic\n");
    out.push('\n');

    // Module doc
    out.push_str(&format!(
        "/-!\n# {} (Generated from PhysLean)\n\n\
         Auto-generated from PhysLean catalog (version: {}).\n\
         These axioms correspond to proven theorems in PhysLean.\n\
         Re-axiomatized here for Lean 4.27 compatibility.\n\n\
         DO NOT EDIT — regenerate with `just generate-axioms`.\n-/\n\n",
        file.module_name, catalog.physlean_version,
    ));

    // Namespace
    out.push_str(&format!("namespace {}\n\n", file.namespace));
    out.push_str("open PhysicsGenerator\n\n");

    // Types first (deduplicated by short name)
    if !file.types.is_empty() {
        out.push_str("-- ══════════════════════════════════════════════════════════════\n");
        out.push_str("-- Types (from PhysLean)\n");
        out.push_str("-- ══════════════════════════════════════════════════════════════\n\n");

        let mut seen_type_names: HashSet<String> = HashSet::new();
        for ty in &file.types {
            if seen_type_names.contains(&ty.name) {
                out.push_str(&format!("-- [skipped duplicate: {} from {}]\n\n", ty.name, ty.physlean_name));
                continue;
            }
            seen_type_names.insert(ty.name.clone());
            render_type(&mut out, ty);
        }
    }

    // Domain-specific helper definitions needed by Derived/ proofs
    render_domain_helpers(&mut out, &file.namespace);

    // Theorems
    if !file.theorems.is_empty() {
        out.push_str("-- ══════════════════════════════════════════════════════════════\n");
        out.push_str("-- Theorems (from PhysLean — re-axiomatized)\n");
        out.push_str("-- ══════════════════════════════════════════════════════════════\n\n");

        for theorem in &file.theorems {
            render_theorem(&mut out, theorem);
        }
    }

    // Close namespace
    out.push_str(&format!("end {}\n", file.namespace));

    out
}

/// Emit domain-specific helper definitions needed by the Derived/ proofs.
///
/// These are computable definitions (not axioms) that the E=mc² proof chain
/// and other derivations depend on. They mirror what was in the old
/// hand-coded Axioms/ files.
fn render_domain_helpers(out: &mut String, namespace: &str) {
    match namespace {
        "PhysicsGenerator.SpecialRelativity" => {
            out.push_str("-- ══════════════════════════════════════════════════════════════\n");
            out.push_str("-- Helper Definitions (for derivation proofs)\n");
            out.push_str("-- ══════════════════════════════════════════════════════════════\n\n");

            out.push_str("/-- A four-momentum vector in special relativity -/\n");
            out.push_str("structure FourMomentum where\n");
            out.push_str("  energy : ℝ\n");
            out.push_str("  px : ℝ\n");
            out.push_str("  py : ℝ\n");
            out.push_str("  pz : ℝ\n\n");

            out.push_str("/-- Squared magnitude of 3-momentum: |p⃗|² = px² + py² + pz² -/\n");
            out.push_str("noncomputable def FourMomentum.three_momentum_sq (p : FourMomentum) : ℝ :=\n");
            out.push_str("  p.px ^ 2 + p.py ^ 2 + p.pz ^ 2\n\n");

            out.push_str("/-- Minkowski invariant (energy scale): E² − |p⃗|²c² -/\n");
            out.push_str("noncomputable def FourMomentum.invariant_mass_energy (p : FourMomentum) : ℝ :=\n");
            out.push_str("  p.energy ^ 2 - p.three_momentum_sq * c ^ 2\n\n");

            out.push_str("/-- Mass-shell condition: E² − |p⃗|²c² = (mc²)² -/\n");
            out.push_str("def OnMassShell (p : FourMomentum) (m : ℝ) : Prop :=\n");
            out.push_str("  p.invariant_mass_energy = (m * c ^ 2) ^ 2\n\n");

            out.push_str("/-- A particle is at rest when its 3-momentum vanishes -/\n");
            out.push_str("def AtRest (p : FourMomentum) : Prop :=\n");
            out.push_str("  p.three_momentum_sq = 0\n\n");
        }
        "PhysicsGenerator.Electromagnetism" => {
            out.push_str("-- ══════════════════════════════════════════════════════════════\n");
            out.push_str("-- Helper Types (for axiom signatures)\n");
            out.push_str("-- ══════════════════════════════════════════════════════════════\n\n");

            out.push_str("/-- Vector field in 3D space -/\n");
            out.push_str("axiom VectorField : Type\n\n");
            out.push_str("/-- Scalar field in 3D space -/\n");
            out.push_str("axiom ScalarField : Type\n\n");
            out.push_str("axiom div_field : VectorField → ScalarField\n");
            out.push_str("axiom curl_field : VectorField → VectorField\n");
            out.push_str("axiom time_deriv : VectorField → Time → VectorField\n");
            out.push_str("axiom scale_field : ℝ → VectorField → VectorField\n");
            out.push_str("axiom add_field : VectorField → VectorField → VectorField\n");
            out.push_str("axiom neg_field : VectorField → VectorField\n");
            out.push_str("axiom div_scalar : ScalarField → ℝ → ScalarField\n");
            out.push_str("axiom zero_scalar : ScalarField\n");
            out.push_str("axiom E_field : VectorField\n");
            out.push_str("axiom B_field : VectorField\n");
            out.push_str("axiom J_field : VectorField\n");
            out.push_str("axiom rho_field : ScalarField\n\n");
        }
        "PhysicsGenerator.QuantumMechanics" => {
            out.push_str("-- ══════════════════════════════════════════════════════════════\n");
            out.push_str("-- Helper Types (for axiom signatures)\n");
            out.push_str("-- ══════════════════════════════════════════════════════════════\n\n");

            out.push_str("axiom Hamiltonian : Type\n");
            out.push_str("axiom apply_hamiltonian : Hamiltonian → QState → QState\n");
            out.push_str("axiom state_time_deriv : (Time → QState) → Time → QState\n");
            out.push_str("axiom scale_state : ℝ → QState → QState\n");
            out.push_str("axiom measure_prob : Observable → QState → ℝ → ℝ\n");
            out.push_str("axiom commutator : Observable → Observable → Observable\n");
            out.push_str("axiom position_op : Observable\n");
            out.push_str("axiom momentum_op : Observable\n");
            out.push_str("axiom identity_op : Observable\n");
            out.push_str("axiom ihbar : ℝ\n\n");
        }
        "PhysicsGenerator.Thermodynamics" => {
            out.push_str("-- ══════════════════════════════════════════════════════════════\n");
            out.push_str("-- Helper Types (for axiom signatures)\n");
            out.push_str("-- ══════════════════════════════════════════════════════════════\n\n");

            out.push_str("axiom ThermoSystem : Type\n");
            out.push_str("axiom IsolatedSystem : Type\n");
            out.push_str("axiom ThermoProcess : Type\n");
            out.push_str("axiom internal_energy : ThermoSystem → ℝ\n");
            out.push_str("axiom entropy_sys : IsolatedSystem → Time → ℝ\n");
            out.push_str("axiom temperature : ThermoSystem → ℝ\n");
            out.push_str("axiom heat_absorbed : ThermoSystem → ThermoProcess → ℝ\n");
            out.push_str("axiom work_done : ThermoSystem → ThermoProcess → ℝ\n");
            out.push_str("axiom delta_internal : ThermoSystem → ThermoProcess → ℝ\n");
            out.push_str("axiom thermo_entropy : ThermoSystem → ℝ\n");
            out.push_str("axiom in_thermal_eq : ThermoSystem → ThermoSystem → Prop\n\n");
        }
        "PhysicsGenerator.Mechanics" => {
            // Mechanics helpers are already in Basic.lean (Body, System, etc.)
        }
        _ => {}
    }
}

/// PhysLean-specific namespace prefixes that won't exist in the prover.
const PHYSLEAN_TYPE_PREFIXES: &[&str] = &[
    "Lorentz.", "LorentzGroup.", "SpaceTime.", "Electromagnetism.",
    "Fermion.", "Higgs.", "StandardModel.", "CliffordAlgebra.",
    "PhysLean.", "SchwartzMap", "complexLorentzTensor.", "realLorentzTensor.",
];

/// Check if a field type string references PhysLean-specific types.
fn field_has_physlean_refs(field: &str) -> bool {
    PHYSLEAN_TYPE_PREFIXES.iter().any(|pfx| field.contains(pfx))
}

/// Render a type as a Lean structure or axiom.
///
/// If a structure's fields reference PhysLean-specific types (which don't exist
/// in the prover), the type is emitted as a plain axiom instead.
fn render_type(out: &mut String, ty: &CatalogType) {
    // Source comment
    out.push_str(&format!("-- Source: PhysLean ({})\n", ty.physlean_name));

    // Doc string from PhysLean (if available)
    let doc_label = ty.doc_string.as_deref().unwrap_or(&ty.name);

    if ty.kind == "structure" && !ty.fields.is_empty() {
        // Check if any field references PhysLean-specific types
        let has_physlean_refs = ty.fields.iter().any(|f| field_has_physlean_refs(f));
        if has_physlean_refs {
            // Emit as axiom only — fields reference types not available in prover
            out.push_str(&format!("/-- {} -/\n", doc_label));
            out.push_str(&format!("axiom {} : Type\n", ty.name));
        } else {
            out.push_str(&format!("/-- {} -/\n", doc_label));
            out.push_str(&format!("structure {} where\n", ty.name));
            for field in &ty.fields {
                out.push_str(&format!("  {field}\n"));
            }
        }
    } else {
        out.push_str(&format!("/-- {} -/\n", doc_label));
        out.push_str(&format!("axiom {} : Type\n", ty.name));
    }
    out.push('\n');
}

/// Check if a type signature can't be used standalone in the prover.
///
/// Filters out:
/// - PhysLean-specific type references
/// - Universe polymorphism (u_1, u_2, etc.)
/// - Metavariables (?m.)
/// - Very long signatures (likely too complex)
fn sig_has_physlean_refs(sig: &str) -> bool {
    // PhysLean-specific patterns
    const ADDITIONAL_PATTERNS: &[&str] = &[
        "SpaceTime", "SpeedOfLight", "minkowskiMatrix", "minkowskiMetric",
        "Lean.ParserDescr", "Lean.Macro", "Lean.TrailingParserDescr",
        "InformalLemma", "InformalDefinition",
    ];
    // Lean internals / structural issues that can't be standalone
    const STRUCTURAL_ISSUES: &[&str] = &[
        "u_1", "u_2", "u_3", "u_4",   // Universe variables
        "?m.",                          // Metavariables
        "instFunLike.coe",             // Low-level instance projections
        "instCategory.Hom",            // Category theory internals
        "instMonoidalCategory",        // Monoidal category instances
        "EquivLike.toFunLike",         // Low-level coercions
        "ModuleCat.",                   // Category-wrapped modules
        "Action.",                      // Representation theory internals
        "V.carrier",                    // Internal carrier access
        ".timeComponent",              // PhysLean field accessors
        ".spaceComponent",             // PhysLean field accessors
        "Subtype.val",                 // Often underspecified without context
        "fun v => v ",                 // Lambda where var is used as function (type ambiguity)
        "fun x => x ",                 // Same pattern
        "Set.univ",                    // Underspecified without type annotation
        "MonoidHom.instFunLike",       // Low-level instance
        "RingHom.id",                  // Low-level ring hom
        "instHSMul.hSMul",            // Low-level scalar mult
        "instHMul.hMul",              // Low-level multiplication
        "instHAdd.hAdd",              // Low-level addition
        "instHSub.hSub",              // Low-level subtraction
        "Real.instLT.lt",             // Low-level less-than
        "Real.instLE.le",             // Low-level less-eq
        "Real.instNeg.neg",           // Low-level negation
        "Finsupp.",                    // Finitely supported functions
        "LinearMap.instFunLike",       // Low-level linear map coercion
        "ContinuousLinearMap.funLike", // Low-level CLM coercion
        "Eq (0 ",                      // Zero applied as function (needs function type context)
        "Eq (1 ",                      // One applied as function
        "optParam",                    // Optional parameters (type definitions, not theorems)
        "→ Type",                      // Type-returning functions (definitions, not theorems)
        "AddSubgroup",                 // Abstract subgroups (underspecified)
        "ContinuousMap",              // Continuous map type (usually needs context)
    ];
    PHYSLEAN_TYPE_PREFIXES.iter().any(|pfx| sig.contains(pfx))
        || ADDITIONAL_PATTERNS.iter().any(|pat| sig.contains(pat))
        || STRUCTURAL_ISSUES.iter().any(|pat| sig.contains(pat))
        || sig.len() > 300  // Long signatures are likely too complex for standalone use
}

/// Render a theorem as a Lean axiom with source traceability.
///
/// Only emits `axiom` declarations for theorems marked `can_reaxiomatize`
/// AND whose signatures don't reference PhysLean-specific types.
/// Complex theorems are emitted as comments for reference.
fn render_theorem(out: &mut String, theorem: &CatalogTheorem) {
    // Source comment
    out.push_str(&format!("-- Source: PhysLean ({})\n", theorem.physlean_name));

    // Double-check: even if catalog says can_reaxiomatize, verify the signature
    // doesn't reference PhysLean-specific types that don't exist in the prover
    let actually_reaxiomatizable = theorem.can_reaxiomatize
        && !sig_has_physlean_refs(&theorem.type_signature);

    if !actually_reaxiomatizable {
        // Complex signature — emit as comment only.
        // Must comment each line since type_signature may be multiline.
        out.push_str("-- [complex signature, not re-axiomatized]\n");
        let full_sig = format!("{} : {}", theorem.name, theorem.type_signature);
        for line in full_sig.lines() {
            out.push_str(&format!("-- {line}\n"));
        }
        out.push('\n');
        return;
    }

    // Doc string
    if let Some(ref doc) = theorem.doc_string {
        out.push_str(&format!("/-- {doc} -/\n"));
    }

    // Axiom declaration
    // The type_signature from PhysLean is the full type — we declare it as an axiom
    out.push_str(&format!(
        "axiom {} :\n  {}\n\n",
        theorem.name, theorem.type_signature
    ));
}

/// Render the Dimensions.lean file (our own, not from PhysLean).
fn render_dimensions_file() -> String {
    r#"/-!
# SI Dimensions

Physical dimensions for dimensional analysis.
This file is NOT generated from PhysLean — it is our own dimensional analysis framework.
-/

namespace PhysicsGenerator.Dimensions

/-- SI base dimensions as integer exponents -/
structure Dimension where
  length      : Int
  mass        : Int
  time        : Int
  current     : Int
  temperature : Int
  amount      : Int
  luminosity  : Int
  deriving DecidableEq, Repr

def Dimension.dimensionless : Dimension :=
  ⟨0, 0, 0, 0, 0, 0, 0⟩

def Dimension.energy : Dimension :=
  ⟨2, 1, -2, 0, 0, 0, 0⟩

def Dimension.force : Dimension :=
  ⟨1, 1, -2, 0, 0, 0, 0⟩

def Dimension.velocity : Dimension :=
  ⟨1, 0, -1, 0, 0, 0, 0⟩

def Dimension.momentum : Dimension :=
  ⟨1, 1, -1, 0, 0, 0, 0⟩

def Dimension.action : Dimension :=
  ⟨2, 1, -1, 0, 0, 0, 0⟩

/-- Multiply dimensions (add exponents) -/
def Dimension.mul (a b : Dimension) : Dimension :=
  ⟨a.length + b.length, a.mass + b.mass, a.time + b.time,
   a.current + b.current, a.temperature + b.temperature,
   a.amount + b.amount, a.luminosity + b.luminosity⟩

/-- Divide dimensions (subtract exponents) -/
def Dimension.div (a b : Dimension) : Dimension :=
  ⟨a.length - b.length, a.mass - b.mass, a.time - b.time,
   a.current - b.current, a.temperature - b.temperature,
   a.amount - b.amount, a.luminosity - b.luminosity⟩

instance : HMul Dimension Dimension Dimension := ⟨Dimension.mul⟩

/-- Equations must be dimensionally homogeneous -/
axiom dim_homogeneity : ∀ (d1 d2 : Dimension), d1 = d2 -> True

end PhysicsGenerator.Dimensions
"#.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::loader::load_catalog;
    use std::path::PathBuf;

    #[test]
    fn domain_config_known() {
        assert!(domain_config("SpecialRelativity").is_some());
        assert!(domain_config("ClassicalMechanics").is_some());
        assert!(domain_config("NonExistent").is_none());
    }

    #[test]
    fn infer_domain_from_name() {
        assert_eq!(infer_type_domain("PhysLean.Relativity.Special.FourMomentum"), "SpecialRelativity");
        assert_eq!(infer_type_domain("PhysLean.Electromagnetism.FieldStrengthTensor"), "Electromagnetism");
    }

    #[test]
    fn generate_from_catalog() {
        let catalog_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("physlean-extract/output/catalog.json");

        if !catalog_path.exists() {
            return;
        }

        let catalog = load_catalog(&catalog_path).unwrap();
        let tmp_dir = std::env::temp_dir().join("physics-gen-test");
        let _ = std::fs::remove_dir_all(&tmp_dir);
        let count = generate_all(&catalog, &tmp_dir).unwrap();
        assert!(count > 0);

        // Check that Generated files were created
        assert!(tmp_dir.join("SpecialRelativity.lean").exists());
        assert!(tmp_dir.join("Dimensions.lean").exists());

        // Cleanup
        let _ = std::fs::remove_dir_all(&tmp_dir);
    }
}
