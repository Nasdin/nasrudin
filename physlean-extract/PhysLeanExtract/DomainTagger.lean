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
  | Electromagnetism
  | QuantumMechanics
  | Thermodynamics
  | StatisticalMechanics
  | PureMath
  | Unknown
  deriving Inhabited, Repr, BEq

/-- Convert a PhysDomain to its JSON string representation. -/
def PhysDomain.toJsonString : PhysDomain → String
  | .ClassicalMechanics => "ClassicalMechanics"
  | .SpecialRelativity => "SpecialRelativity"
  | .Electromagnetism => "Electromagnetism"
  | .QuantumMechanics => "QuantumMechanics"
  | .Thermodynamics => "Thermodynamics"
  | .StatisticalMechanics => "StatisticalMechanics"
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
  -- Special & general relativity (flat namespace patterns from PhysLean)
  if str.startsWith "Lorentz." ||
     str.startsWith "LorentzGroup." ||
     str.startsWith "SpaceTime." ||
     str.startsWith "minkowskiMatrix." ||
     str.startsWith "complexLorentzTensor." ||
     str.startsWith "realLorentzTensor." then
    .SpecialRelativity
  -- Electromagnetism (flat namespace)
  else if str.startsWith "Electromagnetism." then
    .Electromagnetism
  -- Particle physics / Standard Model → QuantumMechanics
  else if str.startsWith "Fermion." ||
          str.startsWith "Higgs." ||
          str.startsWith "StandardModel." then
    .QuantumMechanics
  -- Clifford algebra → SpecialRelativity (used for spinors)
  else if str.startsWith "CliffordAlgebra." then
    .SpecialRelativity
  -- PhysLean.* prefixed namespaces (original module paths)
  else if str.startsWith "PhysLean.ClassicalMechanics" then
    .ClassicalMechanics
  else if str.startsWith "PhysLean.Relativity" then
    .SpecialRelativity
  else if str.startsWith "PhysLean.SpaceAndTime" then
    .SpecialRelativity
  else if str.startsWith "PhysLean.Electromagnetism" then
    .Electromagnetism
  else if str.startsWith "PhysLean.QuantumMechanics" then
    .QuantumMechanics
  else if str.startsWith "PhysLean.QFT" then
    .QuantumMechanics
  else if str.startsWith "PhysLean.Thermodynamics" then
    .Thermodynamics
  else if str.startsWith "PhysLean.StatisticalMechanics" then
    .StatisticalMechanics
  else if str.startsWith "PhysLean.Mathematics" then
    .PureMath
  else if str.startsWith "PhysLean.Units" then
    .PureMath
  -- Infrastructure / meta / too specialized → Unknown
  else if str.startsWith "PhysLean." then
    .Unknown
  else
    .Unknown

/-- Map a domain to its corresponding Lean import module in our prover. -/
def PhysDomain.toLeanImport : PhysDomain → Option String
  | .ClassicalMechanics => some "PhysicsGenerator.Generated.Mechanics"
  | .SpecialRelativity => some "PhysicsGenerator.Generated.SpecialRelativity"
  | .Electromagnetism => some "PhysicsGenerator.Generated.Electromagnetism"
  | .QuantumMechanics => some "PhysicsGenerator.Generated.QuantumMechanics"
  | .Thermodynamics => some "PhysicsGenerator.Generated.Thermodynamics"
  | .StatisticalMechanics => some "PhysicsGenerator.Generated.Thermodynamics"
  | .PureMath => none
  | .Unknown => none

end PhysLeanExtract
