/-!
# Domain Tagger

Maps PhysLean namespace prefixes to physics domain tags.
Used to categorize extracted theorems for the Rust engine.
-/

import Lean

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
-/
def tagDomain (name : Name) : PhysDomain :=
  let str := name.toString
  if str.startsWith "PhysLean.ClassicalMechanics" then
    .ClassicalMechanics
  else if str.startsWith "PhysLean.Relativity" then
    .SpecialRelativity
  else if str.startsWith "PhysLean.Electromagnetism" then
    .Electromagnetism
  else if str.startsWith "PhysLean.QuantumMechanics" then
    .QuantumMechanics
  else if str.startsWith "PhysLean.Thermodynamics" then
    .Thermodynamics
  else if str.startsWith "PhysLean.StatisticalMechanics" then
    .StatisticalMechanics
  else if str.startsWith "PhysLean.Mathematics" then
    .PureMath
  -- Also handle the broader PhysLean.Meta, PhysLean.Cosmology etc
  else if str.startsWith "PhysLean.Cosmology" then
    -- Cosmology stubs → no domain (PhysLean coverage is minimal)
    .Unknown
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
