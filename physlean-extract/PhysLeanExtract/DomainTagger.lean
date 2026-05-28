import Lean

/-!
# Domain Tagger

Maps PhysLean namespace prefixes to physics domain tags.
Used to categorize extracted theorems for the Rust engine.
-/

namespace PhysLeanExtract

open Lean

/-- Physics domain categories matching the Rust `Domain` enum. -/
inductive PhysDomain where
  | ClassicalMechanics
  | SpecialRelativity
  | GeneralRelativity
  | Electromagnetism
  | QuantumMechanics
  | QuantumFieldTheory
  | Thermodynamics
  | StatisticalMechanics
  | Optics
  | FluidDynamics
  | PureMath
  | Unknown
  deriving Inhabited, Repr, BEq

/-- Convert a PhysDomain to its JSON string representation. The Rust
    importer applies a second, more permissive pass via
    `nasrudin_derive::domain_tagger::resolve_domain` — but emitting
    the right string here means the JSON round-trip is consistent end
    to end, and a future Rust-side simplification won't lose data. -/
def PhysDomain.toJsonString : PhysDomain → String
  | .ClassicalMechanics => "ClassicalMechanics"
  | .SpecialRelativity => "SpecialRelativity"
  | .GeneralRelativity => "GeneralRelativity"
  | .Electromagnetism => "Electromagnetism"
  | .QuantumMechanics => "QuantumMechanics"
  | .QuantumFieldTheory => "QuantumFieldTheory"
  | .Thermodynamics => "Thermodynamics"
  | .StatisticalMechanics => "StatisticalMechanics"
  | .Optics => "Optics"
  | .FluidDynamics => "FluidDynamics"
  | .PureMath => "PureMath"
  | .Unknown => "Unknown"

/-- Map a PhysLean fully-qualified name to a physics domain.

PhysLean organizes its library under:
- `PhysLean.ClassicalMechanics.*`
- `PhysLean.Relativity.*` (includes both special & general)
- `PhysLean.Electromagnetism.*`
- `PhysLean.QuantumMechanics.*`
- `PhysLean.Thermodynamics.*`
- `PhysLean.StatisticalMechanics.*`
- `PhysLean.Mathematics.*` (supporting math)
- `PhysLean.SpaceAndTime.*` (spacetime geometry)
- `PhysLean.QFT.*` (quantum field theory)
- `PhysLean.Particles.*` (particle physics)
- `PhysLean.Units.*` (unit systems)
- `PhysLean.Meta.*` (metaprogramming)
-/
def tagDomain (name : Name) : PhysDomain :=
  let str := name.toString
  -- Special relativity / Lorentz machinery (flat-namespace patterns)
  if str.startsWith "Lorentz." ||
     str.startsWith "LorentzGroup." ||
     str.startsWith "SpaceTime." ||
     str.startsWith "Spacetime." ||
     str.startsWith "minkowskiMatrix." ||
     str.startsWith "complexLorentzTensor." ||
     str.startsWith "realLorentzTensor." ||
     str.startsWith "CliffordAlgebra." ||
     str.startsWith "Space." ||
     str.startsWith "PhysLean.Relativity" ||
     str.startsWith "PhysLean.SpaceAndTime" then
    .SpecialRelativity
  -- General relativity & cosmology — FLRW, Friedmann equations,
  -- spatial geometry all live under `Cosmology.*` in PhysLean v4.26.0
  else if str.startsWith "Cosmology." ||
          str.startsWith "PhysLean.Cosmology" ||
          str.startsWith "FLRW." ||
          str.startsWith "FriedmannEquation." ||
          str.startsWith "GeneralRelativity." ||
          str.startsWith "PhysLean.GeneralRelativity" then
    .GeneralRelativity
  -- Classical mechanics — flat sub-namespaces alongside
  -- `ClassicalMechanics.*` / `PhysLean.ClassicalMechanics.*`
  else if str.startsWith "ClassicalMechanics." ||
          str.startsWith "PhysLean.ClassicalMechanics" ||
          str.startsWith "HarmonicOscillator." ||
          str.startsWith "Pendulum." ||
          str.startsWith "RigidBody." ||
          str.startsWith "Scattering." ||
          str.startsWith "WaveEquation." ||
          str.startsWith "Vibrations." then
    .ClassicalMechanics
  -- Electromagnetism
  else if str.startsWith "Electromagnetism." ||
          str.startsWith "PhysLean.Electromagnetism" then
    .Electromagnetism
  -- Optics
  else if str.startsWith "Optics." ||
          str.startsWith "PhysLean.Optics" then
    .Optics
  -- Thermodynamics — PhysLean v4.26.0 ships `Temperature.*` and
  -- `TemperatureUnit.*` as the bare-namespace forms.
  else if str.startsWith "Thermodynamics." ||
          str.startsWith "PhysLean.Thermodynamics" ||
          str.startsWith "Temperature." ||
          str.startsWith "TemperatureUnit." ||
          str.startsWith "BlackBody." ||
          str.startsWith "ThermalSystem." ||
          str.startsWith "Entropy." then
    .Thermodynamics
  -- Statistical mechanics & condensed matter
  else if str.startsWith "StatisticalMechanics." ||
          str.startsWith "PhysLean.StatisticalMechanics" ||
          str.startsWith "CondensedMatter." ||
          str.startsWith "PhysLean.CondensedMatter" ||
          str.startsWith "TightBindingChain." ||
          str.startsWith "CanonicalEnsemble." then
    .StatisticalMechanics
  -- Quantum field theory & particle physics — PhysLean's largest
  -- physics surface (FieldSpecification, WickContraction,
  -- TensorSpecies, PureU1 anomaly cancellation, Standard Model,
  -- Higgs, Fermion, FTheory/strings, SuperSymmetry, SMRHN, Action).
  else if str.startsWith "QFT." ||
          str.startsWith "PhysLean.QFT" ||
          str.startsWith "QuantumFieldTheory." ||
          str.startsWith "FieldSpecification." ||
          str.startsWith "WickContraction." ||
          str.startsWith "TensorSpecies." ||
          str.startsWith "PureU1." ||
          str.startsWith "StandardModel." ||
          str.startsWith "Higgs." ||
          str.startsWith "Fermion." ||
          str.startsWith "SuperSymmetry." ||
          str.startsWith "FTheory." ||
          str.startsWith "SMRHN." ||
          str.startsWith "Action." ||
          str.startsWith "AnomalyCancellation." ||
          str.startsWith "BeyondTheStandardModel." ||
          str.startsWith "FlavorPhysics." ||
          str.startsWith "NeutrinoPhysics." ||
          str.startsWith "PhysLean.Particles" ||
          str.startsWith "Particles." ||
          str.startsWith "PhysLean.StringTheory" ||
          str.startsWith "StringTheory." ||
          str.startsWith "PhysLean.AnomalyCancellation" then
    .QuantumFieldTheory
  -- Quantum mechanics (single-particle, finite-dim) — also includes
  -- the QM substrate (inner-product spaces, Hilbert, Schwartz maps)
  -- so a QM island's `seed_from_axioms(by_domain(QM))` has material
  -- to evolve from.
  else if str.startsWith "QuantumMechanics." ||
          str.startsWith "PhysLean.QuantumMechanics" ||
          str.startsWith "InnerProductSpace." ||
          str.startsWith "Hilbert." ||
          str.startsWith "SchwartzMap." then
    .QuantumMechanics
  -- Fluid dynamics (empty in PhysLean v4.26.0 but reserved)
  else if str.startsWith "FluidDynamics." ||
          str.startsWith "PhysLean.FluidDynamics" then
    .FluidDynamics
  else if str.startsWith "PhysLean.Mathematics" then
    .PureMath
  else if str.startsWith "PhysLean.Units" then
    .PureMath
  -- Mathlib quantum-relevant namespaces — these are the substrate the
  -- GA needs in scope when evolving QM theorems (operator algebra,
  -- inner products, self-adjointness, spectral theory, tensor
  -- products of state spaces, normed/Banach/Hilbert structure,
  -- complex numbers underpinning amplitudes).
  --
  -- Tagging them as `.QuantumMechanics` rather than `.PureMath` means
  -- a QM-domain island's `seed_from_axioms(store.by_domain(QM))` will
  -- actually pull these as starting individuals, instead of seeing
  -- only the empty PhysLean QM-namespace surface (Higgs/Fermion/SM).
  else if str.startsWith "Mathlib.Analysis.InnerProductSpace." ||
          str.startsWith "Mathlib.Analysis.Normed.Module." ||
          str.startsWith "Mathlib.Analysis.NormedSpace.Spectrum." ||
          str.startsWith "Mathlib.Analysis.NormedSpace.OperatorNorm." ||
          str.startsWith "Mathlib.Analysis.Hilbert" ||
          str.startsWith "Mathlib.LinearAlgebra.SelfAdjoint" ||
          str.startsWith "Mathlib.LinearAlgebra.Matrix.Hermitian" ||
          str.startsWith "Mathlib.LinearAlgebra.Matrix.Spectrum" ||
          str.startsWith "Mathlib.LinearAlgebra.TensorProduct." ||
          str.startsWith "Mathlib.LinearAlgebra.Eigenspace" ||
          str.startsWith "Mathlib.Topology.ContinuousFunction.Algebra." ||
          str.startsWith "Complex." then
    .QuantumMechanics
  -- Mathlib measure-theory and probability stay as PureMath — they
  -- support QM (Born rule, expectation values) but are also broadly
  -- used in classical statistical mechanics. The chain-engine sees
  -- them via the full AxiomStore regardless of tag. Also: bare-name
  -- Mathlib namespaces (`Real.`, `Nat.`, `Int.`, `Rat.`) which are
  -- heavily used algebraic helpers.
  else if str.startsWith "Mathlib." ||
          str.startsWith "Real." ||
          str.startsWith "Nat." ||
          str.startsWith "Int." ||
          str.startsWith "Rat." ||
          str.startsWith "Set." ||
          str.startsWith "Function." ||
          str.startsWith "Order." ||
          str.startsWith "List." ||
          str.startsWith "Finset." ||
          str.startsWith "Filter." ||
          str.startsWith "Equiv." ||
          str.startsWith "Group." ||
          str.startsWith "Ring." ||
          str.startsWith "Module." ||
          str.startsWith "Topology." then
    .PureMath
  -- Infrastructure / meta / too specialized → Unknown
  else if str.startsWith "PhysLean." then
    .Unknown
  else
    -- Anything else extracted under the +mathlib whitelist is math —
    -- conservative default (was Unknown).
    .PureMath

/-- Map a domain to its corresponding Lean import module in our prover. -/
def PhysDomain.toLeanImport : PhysDomain → Option String
  | .ClassicalMechanics => some "PhysicsGenerator.Generated.Mechanics"
  | .SpecialRelativity => some "PhysicsGenerator.Generated.SpecialRelativity"
  | .GeneralRelativity => some "PhysicsGenerator.Generated.SpecialRelativity"
  | .Electromagnetism => some "PhysicsGenerator.Generated.Electromagnetism"
  | .QuantumMechanics => some "PhysicsGenerator.Generated.QuantumMechanics"
  | .QuantumFieldTheory => some "PhysicsGenerator.Generated.QuantumMechanics"
  | .Thermodynamics => some "PhysicsGenerator.Generated.Thermodynamics"
  | .StatisticalMechanics => some "PhysicsGenerator.Generated.Thermodynamics"
  | .Optics => some "PhysicsGenerator.Generated.Electromagnetism"
  | .FluidDynamics => some "PhysicsGenerator.Generated.Mechanics"
  | .PureMath => none
  | .Unknown => none

end PhysLeanExtract
