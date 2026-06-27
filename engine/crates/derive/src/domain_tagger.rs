//! Physics-domain tagging from a Lean kernel name.
//!
//! PhysLean uses both `PhysLean.<Area>.…` and bare flat namespaces
//! like `ClassicalMechanics.HarmonicOscillator.…`, `Cosmology.FLRW.…`,
//! `FieldSpecification.…`, etc. The Lean-side `DomainTagger` only
//! matched the `PhysLean.<Area>` form, so every flat-namespace
//! PhysLean theorem fell through to `PureMath`. As a result the
//! corpus showed 0 ClassicalMechanics / 0 Thermodynamics /
//! 0 StatisticalMechanics / 0 GeneralRelativity entries even though
//! PhysLean ships hundreds of theorems in each area.
//!
//! This module is the *Rust* source of truth: it owns the
//! prefix→`Domain` mapping and is invoked by every importer
//! (`physlean_import::parse_entry`, `axiom_store::parse_catalog_theorem`)
//! so the JSON `domain` field is treated as a hint and re-checked
//! locally. The Lean `DomainTagger` should mirror this list, but
//! correctness no longer depends on it — the Rust side overrides any
//! stale JSON tag.

use nasrudin_core::Domain;

/// Tag a physics `Domain` from a Lean kernel name (e.g.
/// `"ClassicalMechanics.HarmonicOscillator.k_pos"`).
///
/// Returns `None` if the name doesn't match any known physics
/// namespace prefix. The caller falls back to `Domain::PureMath` in
/// that case, but distinguishing "genuinely PureMath" from "no match"
/// matters for upstream sources that ship explicit `domain` strings
/// we may want to honour.
pub fn tag_domain_from_name(name: &str) -> Option<Domain> {
    // ── Special relativity ─────────────────────────────────────────
    // Lorentz tensors, spacetime, the Lorentz/Poincaré group,
    // Clifford algebras (used for spinors), and the raw Minkowski
    // metric all live in flat namespaces. Tagging them SR collects
    // them on the SR island.
    if has_prefix(
        name,
        &[
            "Lorentz.",
            "LorentzGroup.",
            "SpaceTime.",
            "Spacetime.",
            "minkowskiMatrix.",
            "complexLorentzTensor.",
            "realLorentzTensor.",
            "CliffordAlgebra.",
            "Space.",
            "PhysLean.Relativity.",
            "PhysLean.SpaceAndTime.",
        ],
    ) {
        return Some(Domain::SpecialRelativity);
    }

    // ── General relativity & cosmology ─────────────────────────────
    // FLRW, Friedmann equations, Hubble constant, spatial geometry
    // all live under `Cosmology.*` in PhysLean v4.26.0.
    if has_prefix(
        name,
        &[
            "Cosmology.",
            "PhysLean.Cosmology.",
            "FLRW.",
            "FriedmannEquation.",
            "GeneralRelativity.",
            "PhysLean.GeneralRelativity.",
        ],
    ) {
        return Some(Domain::GeneralRelativity);
    }

    // ── Classical mechanics ────────────────────────────────────────
    // PhysLean ships harmonic oscillator, pendulum, rigid body,
    // wave equation, scattering, vibrations all directly under
    // `ClassicalMechanics.*` (flat) or transitively under
    // `PhysLean.ClassicalMechanics.*`. The bare names
    // (HarmonicOscillator.foo) appear when PhysLean uses
    // `namespace HarmonicOscillator` inside a ClassicalMechanics
    // file.
    if has_prefix(
        name,
        &[
            "ClassicalMechanics.",
            "PhysLean.ClassicalMechanics.",
            "HarmonicOscillator.",
            "Pendulum.",
            "RigidBody.",
            "Scattering.",
            "WaveEquation.",
            "Vibrations.",
        ],
    ) {
        return Some(Domain::ClassicalMechanics);
    }

    // ── Electromagnetism ───────────────────────────────────────────
    if has_prefix(name, &["Electromagnetism.", "PhysLean.Electromagnetism."]) {
        return Some(Domain::Electromagnetism);
    }

    // ── Optics ─────────────────────────────────────────────────────
    if has_prefix(name, &["Optics.", "PhysLean.Optics."]) {
        return Some(Domain::Optics);
    }

    // ── Thermodynamics ─────────────────────────────────────────────
    // PhysLean v4.26.0 ships `Thermodynamics/IdealGas/*.lean` and
    // `Thermodynamics/Temperature/*.lean` (namespaces `Temperature`,
    // `TemperatureUnit`). `IdealGas` is under
    // `Thermodynamics.IdealGas.*` (caught by `Thermodynamics.`
    // prefix).
    if has_prefix(
        name,
        &[
            "Thermodynamics.",
            "PhysLean.Thermodynamics.",
            "Temperature.",
            "TemperatureUnit.",
            "BlackBody.",
            "ThermalSystem.",
            "Entropy.",
        ],
    ) {
        return Some(Domain::Thermodynamics);
    }

    // ── Statistical mechanics & condensed matter ───────────────────
    if has_prefix(
        name,
        &[
            "StatisticalMechanics.",
            "PhysLean.StatisticalMechanics.",
            "CondensedMatter.",
            "PhysLean.CondensedMatter.",
            "TightBindingChain.",
            "CanonicalEnsemble.",
        ],
    ) {
        return Some(Domain::StatisticalMechanics);
    }

    // ── Quantum field theory & particle physics ────────────────────
    // PhysLean's largest physics surface: FieldSpecification (field
    // operator algebra), WickContraction, TensorSpecies, PureU1
    // anomaly cancellation, Standard Model, Higgs, Fermion, FTheory
    // (string-theory), SuperSymmetry, SMRHN (Standard Model right-
    // handed neutrinos), Action principles, BeyondTheStandardModel,
    // FlavorPhysics, NeutrinoPhysics. All QFT-adjacent.
    if has_prefix(
        name,
        &[
            "QFT.",
            "PhysLean.QFT.",
            "QuantumFieldTheory.",
            "FieldSpecification.",
            "WickContraction.",
            "TensorSpecies.",
            "PureU1.",
            "StandardModel.",
            "Higgs.",
            "Fermion.",
            "SuperSymmetry.",
            "FTheory.",
            "SMRHN.",
            "Action.",
            "AnomalyCancellation.",
            "BeyondTheStandardModel.",
            "FlavorPhysics.",
            "NeutrinoPhysics.",
            "PhysLean.Particles.",
            "Particles.",
            "PhysLean.StringTheory.",
            "StringTheory.",
            "PhysLean.AnomalyCancellation.",
        ],
    ) {
        return Some(Domain::QuantumFieldTheory);
    }

    // ── Quantum mechanics ──────────────────────────────────────────
    // Bare QM (single-particle, finite-dim) lives at
    // `QuantumMechanics.*`. Mathlib's quantum-relevant analysis
    // machinery appears under FLAT names in the corpus (not the
    // `Mathlib.Analysis.*` form): `InnerProductSpace.*`,
    // `SchwartzMap.*` (distributions used in QM), `Hilbert.*` if
    // present. Including them as QM substrate makes a QM-island's
    // `seed_from_axioms(by_domain(QM))` materially richer.
    if has_prefix(
        name,
        &[
            "QuantumMechanics.",
            "PhysLean.QuantumMechanics.",
            "InnerProductSpace.",
            "Hilbert.",
            "SchwartzMap.",
            // Keep the Mathlib-prefixed forms in case a future
            // extraction emits the full path.
            "Mathlib.Analysis.InnerProductSpace.",
            "Mathlib.Analysis.Normed.Module.",
            "Mathlib.Analysis.NormedSpace.Spectrum.",
            "Mathlib.Analysis.NormedSpace.OperatorNorm.",
            "Mathlib.Analysis.Hilbert",
            "Mathlib.LinearAlgebra.SelfAdjoint",
            "Mathlib.LinearAlgebra.Matrix.Hermitian",
            "Mathlib.LinearAlgebra.Matrix.Spectrum",
            "Mathlib.LinearAlgebra.TensorProduct.",
            "Mathlib.LinearAlgebra.Eigenspace",
            "Mathlib.Topology.ContinuousFunction.Algebra.",
        ],
    ) {
        return Some(Domain::QuantumMechanics);
    }

    // ── Fluid dynamics ─────────────────────────────────────────────
    if has_prefix(name, &["FluidDynamics.", "PhysLean.FluidDynamics."]) {
        return Some(Domain::FluidDynamics);
    }

    None
}

/// Tag from a name, falling back to `Domain::PureMath`.
///
/// This is the form `parse_catalog_theorem` and `parse_entry` should
/// call: it never returns `None`.
pub fn tag_domain_or_pure_math(name: &str) -> Domain {
    tag_domain_from_name(name).unwrap_or(Domain::PureMath)
}

/// Resolve a `Domain` for a JSON catalog entry. Tries the
/// `physlean_name` first (the original kernel name), then the
/// normalized `name`, then the JSON-supplied `domain` string, then
/// `PureMath`.
///
/// This is the single entry point importers should use so the rules
/// stay consistent across cold-tier hydration (`math_corpus.json`)
/// and hot-tier registration (`catalog.json`).
pub fn resolve_domain(
    physlean_name: Option<&str>,
    name: &str,
    json_domain: Option<&str>,
) -> Domain {
    // Prefer physlean_name — has the original PascalCase with dots.
    if let Some(pn) = physlean_name {
        if let Some(d) = tag_domain_from_name(pn) {
            return d;
        }
    }
    // Fall back to the normalized `name` — works because we also list
    // lowercase prefixes implicitly by checking dot-form names; but
    // for normalized names like `classicalmechanics_harmonicoscillator_…`
    // we need a separate pass.
    if let Some(d) = tag_domain_from_lowercase_name(name) {
        return d;
    }
    // Finally honour the JSON-emitted string. PhysDomain.toJsonString
    // emits exact PascalCase ("ClassicalMechanics" etc.).
    if let Some(s) = json_domain {
        match s {
            "ClassicalMechanics" => return Domain::ClassicalMechanics,
            "SpecialRelativity" => return Domain::SpecialRelativity,
            "GeneralRelativity" => return Domain::GeneralRelativity,
            "Electromagnetism" => return Domain::Electromagnetism,
            "QuantumMechanics" => return Domain::QuantumMechanics,
            "QuantumFieldTheory" => return Domain::QuantumFieldTheory,
            "Thermodynamics" => return Domain::Thermodynamics,
            "StatisticalMechanics" => return Domain::StatisticalMechanics,
            "Optics" => return Domain::Optics,
            "FluidDynamics" => return Domain::FluidDynamics,
            _ => {}
        }
    }
    Domain::PureMath
}

/// Same rules as `tag_domain_from_name`, but for the lowercase-under-
/// score form emitted into the catalog's `name` field
/// (`classicalmechanics_harmonicoscillator_k_pos` etc.).
fn tag_domain_from_lowercase_name(name: &str) -> Option<Domain> {
    if has_prefix(
        name,
        &[
            "lorentz_",
            "lorentzgroup_",
            "spacetime_",
            "minkowskimatrix_",
            "complexlorentztensor_",
            "reallorentztensor_",
            "cliffordalgebra_",
            "physlean_relativity_",
            "physlean_spaceandtime_",
        ],
    ) {
        return Some(Domain::SpecialRelativity);
    }
    if has_prefix(
        name,
        &[
            "cosmology_",
            "flrw_",
            "friedmannequation_",
            "physlean_cosmology_",
            "generalrelativity_",
            "physlean_generalrelativity_",
        ],
    ) {
        return Some(Domain::GeneralRelativity);
    }
    if has_prefix(
        name,
        &[
            "classicalmechanics_",
            "physlean_classicalmechanics_",
            "harmonicoscillator_",
            "pendulum_",
            "rigidbody_",
            "scattering_",
            "waveequation_",
            "vibrations_",
        ],
    ) {
        return Some(Domain::ClassicalMechanics);
    }
    if has_prefix(name, &["electromagnetism_", "physlean_electromagnetism_"]) {
        return Some(Domain::Electromagnetism);
    }
    if has_prefix(name, &["optics_", "physlean_optics_"]) {
        return Some(Domain::Optics);
    }
    if has_prefix(
        name,
        &[
            "thermodynamics_",
            "physlean_thermodynamics_",
            "temperature_",
            "temperatureunit_",
            "blackbody_",
            "thermalsystem_",
            "entropy_",
        ],
    ) {
        return Some(Domain::Thermodynamics);
    }
    if has_prefix(
        name,
        &[
            "statisticalmechanics_",
            "physlean_statisticalmechanics_",
            "condensedmatter_",
            "physlean_condensedmatter_",
            "tightbindingchain_",
            "canonicalensemble_",
        ],
    ) {
        return Some(Domain::StatisticalMechanics);
    }
    if has_prefix(
        name,
        &[
            "qft_",
            "physlean_qft_",
            "quantumfieldtheory_",
            "fieldspecification_",
            "wickcontraction_",
            "tensorspecies_",
            "pureu1_",
            "standardmodel_",
            "higgs_",
            "fermion_",
            "supersymmetry_",
            "ftheory_",
            "smrhn_",
            "anomalycancellation_",
            "beyondthestandardmodel_",
            "flavorphysics_",
            "neutrinophysics_",
            "physlean_anomalycancellation_",
            "physlean_particles_",
            "particles_",
            "physlean_stringtheory_",
            "stringtheory_",
        ],
    ) {
        return Some(Domain::QuantumFieldTheory);
    }
    if has_prefix(
        name,
        &[
            "quantummechanics_",
            "physlean_quantummechanics_",
            "innerproductspace_",
            "hilbert_",
            "schwartzmap_",
        ],
    ) {
        return Some(Domain::QuantumMechanics);
    }
    if has_prefix(name, &["fluiddynamics_", "physlean_fluiddynamics_"]) {
        return Some(Domain::FluidDynamics);
    }
    None
}

#[inline]
fn has_prefix(s: &str, prefixes: &[&str]) -> bool {
    prefixes.iter().any(|p| s.starts_with(p))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classical_mechanics_bare_namespace() {
        assert_eq!(
            tag_domain_from_name("ClassicalMechanics.HarmonicOscillator.k_pos"),
            Some(Domain::ClassicalMechanics)
        );
        assert_eq!(
            tag_domain_from_name("HarmonicOscillator.energy"),
            Some(Domain::ClassicalMechanics)
        );
        assert_eq!(
            tag_domain_from_name("ClassicalMechanics.WaveEquation"),
            Some(Domain::ClassicalMechanics)
        );
    }

    #[test]
    fn cosmology_flrw_is_general_relativity() {
        assert_eq!(
            tag_domain_from_name("Cosmology.FLRW.FriedmannEquation.hubbleConstant"),
            Some(Domain::GeneralRelativity)
        );
        assert_eq!(
            tag_domain_from_name("FLRW.SpatialGeometry.S"),
            Some(Domain::GeneralRelativity)
        );
    }

    #[test]
    fn thermo_and_statmech_separate() {
        assert_eq!(
            tag_domain_from_name("Thermodynamics.BlackBody.law"),
            Some(Domain::Thermodynamics)
        );
        assert_eq!(
            tag_domain_from_name("StatisticalMechanics.CanonicalEnsemble.Z"),
            Some(Domain::StatisticalMechanics)
        );
        assert_eq!(
            tag_domain_from_name("CanonicalEnsemble.partition"),
            Some(Domain::StatisticalMechanics)
        );
    }

    #[test]
    fn lorentz_is_special_relativity() {
        assert_eq!(
            tag_domain_from_name("Lorentz.CoMod.instAddCommGroup"),
            Some(Domain::SpecialRelativity)
        );
        assert_eq!(
            tag_domain_from_name("LorentzGroup.subtype_mul_inv"),
            Some(Domain::SpecialRelativity)
        );
    }

    #[test]
    fn qft_surfaces_collected() {
        assert_eq!(
            tag_domain_from_name("FieldSpecification.FieldOpFreeAlgebra.foo"),
            Some(Domain::QuantumFieldTheory)
        );
        assert_eq!(
            tag_domain_from_name("StandardModel.Higgs.mass"),
            Some(Domain::QuantumFieldTheory)
        );
        assert_eq!(
            tag_domain_from_name("PureU1.VectorLikeOddPlane.P"),
            Some(Domain::QuantumFieldTheory)
        );
        assert_eq!(
            tag_domain_from_name("WickContraction.pair"),
            Some(Domain::QuantumFieldTheory)
        );
        assert_eq!(
            tag_domain_from_name("FTheory.fiber"),
            Some(Domain::QuantumFieldTheory)
        );
    }

    #[test]
    fn pure_math_falls_through() {
        assert_eq!(tag_domain_from_name("MeasureTheory.intLebesgue"), None);
        assert_eq!(tag_domain_from_name("Polynomial.degree_zero"), None);
        assert_eq!(tag_domain_from_name("Nat.succ_lt"), None);
    }

    #[test]
    fn lowercase_normalized_form_works() {
        assert_eq!(
            tag_domain_from_lowercase_name("classicalmechanics_harmonicoscillator_k_pos"),
            Some(Domain::ClassicalMechanics)
        );
        assert_eq!(
            tag_domain_from_lowercase_name("cosmology_flrw_friedmannequation_hubble"),
            Some(Domain::GeneralRelativity)
        );
        assert_eq!(
            tag_domain_from_lowercase_name("fieldspecification_fieldopfreealgebra_foo"),
            Some(Domain::QuantumFieldTheory)
        );
    }

    #[test]
    fn resolve_domain_prefers_physlean_name() {
        // physlean_name catches it
        assert_eq!(
            resolve_domain(
                Some("ClassicalMechanics.HarmonicOscillator.k_pos"),
                "classicalmechanics_harmonicoscillator_k_pos",
                Some("PureMath"),
            ),
            Domain::ClassicalMechanics,
            "physlean_name override beats the stale 'PureMath' JSON tag"
        );
    }

    #[test]
    fn resolve_domain_falls_back_to_json_when_unknown() {
        // No prefix match anywhere — honour the JSON tag if it's a
        // known string.
        assert_eq!(
            resolve_domain(
                Some("UnknownNs.foo"),
                "unknownns_foo",
                Some("SpecialRelativity")
            ),
            Domain::SpecialRelativity,
        );
        assert_eq!(
            resolve_domain(Some("UnknownNs.foo"), "unknownns_foo", None),
            Domain::PureMath,
        );
    }
}
