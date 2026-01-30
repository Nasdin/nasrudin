/-!
# PhysLean Environment Walker

Walks the Lean environment after importing PhysLean, collecting all
theorem and definition constants. Filters out:
- Constants containing `sorry` in their proof terms
- Constants tagged as `semiformal_result`
- Internal/auxiliary constants (names starting with `_`)
-/

import Lean

namespace PhysLeanExtract

open Lean

/-- Represents an extracted theorem from PhysLean. -/
structure ExtractedTheorem where
  /-- Fully qualified Lean name -/
  name : Name
  /-- Pretty-printed type signature -/
  typeSignature : String
  /-- Whether this is a theorem (vs definition/constant) -/
  isTheorem : Bool
  /-- Doc string if available -/
  docString : Option String
  deriving Inhabited, Repr

/-- Represents an extracted type/structure from PhysLean. -/
structure ExtractedType where
  /-- Fully qualified Lean name -/
  name : Name
  /-- Kind: "structure", "inductive", "def" -/
  kind : String
  /-- Pretty-printed type signature -/
  typeSignature : String
  /-- Field names if structure -/
  fields : Array String
  /-- Doc string if available -/
  docString : Option String
  deriving Inhabited, Repr

/-- Check if a name belongs to PhysLean (not Lean/Mathlib internals). -/
def isPhysLeanName (n : Name) : Bool :=
  let str := n.toString
  str.startsWith "PhysLean."

/-- Check if a name is internal/auxiliary. -/
def isInternalName (n : Name) : Bool :=
  let str := n.toString
  str.containsSubstr "._" ||
  str.containsSubstr ".match_" ||
  str.containsSubstr ".proof_" ||
  str.containsSubstr ".rec" ||
  str.containsSubstr ".brecOn" ||
  str.containsSubstr ".below" ||
  str.containsSubstr ".casesOn" ||
  str.containsSubstr ".recOn" ||
  str.containsSubstr ".noConfusion"

/-- Check if a constant name is tagged as semiformal. -/
def isSemiformal (n : Name) : Bool :=
  let str := n.toString
  str.containsSubstr "semiformal" ||
  str.containsSubstr "Semiformal"

/-- Walk the environment and extract all PhysLean theorems. -/
def walkTheorems (env : Environment) : IO (Array ExtractedTheorem) := do
  let mut results := #[]
  for (name, ci) in env.constants.map₁.toList do
    -- Skip non-PhysLean constants
    unless isPhysLeanName name do continue
    -- Skip internal names
    if isInternalName name then continue
    -- Skip semiformal results
    if isSemiformal name then continue

    match ci with
    | .thmInfo val =>
      -- Check for sorry in the proof value
      let hasSorry := val.value!.hasSorry
      unless hasSorry do
        let fmt ← try
          let opts := Options.empty
          let typeStr := toString (← Lean.Meta.MetaM.run' (ctx := {}) (s := {}) do
            Lean.Meta.ppExpr val.type)
          pure typeStr
        catch _ =>
          pure (toString val.type)
        results := results.push {
          name := name
          typeSignature := fmt
          isTheorem := true
          docString := none
        }
    | .defnInfo val =>
      -- Include key definitions (structures, types)
      let fmt ← try
        let typeStr := toString (← Lean.Meta.MetaM.run' (ctx := {}) (s := {}) do
          Lean.Meta.ppExpr val.type)
        pure typeStr
      catch _ =>
        pure (toString val.type)
      results := results.push {
        name := name
        typeSignature := fmt
        isTheorem := false
        docString := none
      }
    | _ => pure ()

  return results

/-- Walk the environment and extract PhysLean types (structures/inductives). -/
def walkTypes (env : Environment) : IO (Array ExtractedType) := do
  let mut results := #[]
  for (name, ci) in env.constants.map₁.toList do
    unless isPhysLeanName name do continue
    if isInternalName name then continue

    match ci with
    | .inductInfo val =>
      let fmt ← try
        let typeStr := toString (← Lean.Meta.MetaM.run' (ctx := {}) (s := {}) do
          Lean.Meta.ppExpr val.type)
        pure typeStr
      catch _ =>
        pure (toString val.type)

      -- Get constructor fields for structures
      let fields := if val.ctors.length == 1 then
        val.ctors.toArray.map (fun c => c.toString)
      else
        #[]

      results := results.push {
        name := name
        kind := if val.isRec then "inductive" else "structure"
        typeSignature := fmt
        fields := fields
        docString := none
      }
    | _ => pure ()

  return results

end PhysLeanExtract
