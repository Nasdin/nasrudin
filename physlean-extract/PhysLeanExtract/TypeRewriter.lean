import Lean

/-!
# Type Signature Rewriter

Post-processes pretty-printed type signatures from PhysLean:
1. Strips `PhysLean.*` namespace prefixes for readability
2. Classifies signatures as "simple" or "complex"
3. Determines whether a signature can be safely re-axiomatized in our prover

A "simple" signature only references basic Mathlib types (ℝ, ℕ, ℤ, Matrix, Fin, etc.)
and standard Lean constructs. A "complex" signature references PhysLean-specific types
that we can't easily reproduce.
-/

namespace PhysLeanExtract

open Lean

/-- Check if `haystack` contains `needle` as a substring. -/
private def strContains (haystack : String) (needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Known PhysLean namespace prefixes to strip. -/
private def physleanPrefixes : List String :=
  [ "PhysLean.Relativity.Tensors.RealTensor."
  , "PhysLean.Relativity.Special."
  , "PhysLean.Relativity."
  , "PhysLean.SpaceAndTime."
  , "PhysLean.ClassicalMechanics."
  , "PhysLean.Electromagnetism."
  , "PhysLean.QuantumMechanics."
  , "PhysLean.QFT."
  , "PhysLean.Thermodynamics."
  , "PhysLean.StatisticalMechanics."
  , "PhysLean.Mathematics."
  , "PhysLean.Particles."
  , "PhysLean.Units."
  , "PhysLean.Meta."
  , "PhysLean."
  ]

/-- Strip PhysLean namespace prefixes from a type signature string. -/
def stripPhysLeanPrefixes (sig : String) : String :=
  physleanPrefixes.foldl (fun s pfx => s.replace pfx "") sig

/-- Known PhysLean-specific type references that make a signature "complex".
    These are types/names that won't exist in the prover (which only imports Mathlib). -/
private def complexIndicators : List String :=
  [ "PhysLean."
  , "Lorentz"
  , "Tensor"
  , "Clifford"
  , "SpinGroup"
  , "Grassmann"
  , "HiggsField"
  , "StandardModel"
  , "GaugeField"
  , "FermiField"
  , "Manifold"
  , "Bundle"
  , "CategoryTheory"
  -- Flat PhysLean namespace types
  , "SpaceTime"
  , "SpeedOfLight"
  , "minkowskiMatrix"
  , "minkowskiMetric"
  , "Electromagnetism."
  , "Fermion."
  , "Higgs."
  -- PhysLean semiformal/informal markers
  , "InformalLemma"
  , "InformalDefinition"
  -- Lean meta types (shouldn't appear in physics theorems)
  , "Lean.ParserDescr"
  , "Lean.TrailingParserDescr"
  , "Lean.Macro"
  ]

/-- Check if a type signature is "simple" — only references basic types
    that our prover can handle without importing PhysLean. -/
def isSimpleSignature (sig : String) : Bool :=
  let stripped := stripPhysLeanPrefixes sig
  !complexIndicators.any fun indicator => strContains stripped indicator

/-- Rewrite a type signature: strip prefixes and classify.
    Returns (rewritten_signature, can_reaxiomatize). -/
def rewriteTypeSignature (sig : String) : String × Bool :=
  let rewritten := stripPhysLeanPrefixes sig
  let canReax := isSimpleSignature sig
  (rewritten, canReax)

end PhysLeanExtract
