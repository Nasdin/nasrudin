import Lean
import PhysLeanExtract.Walker
import PhysLeanExtract.DomainTagger
import PhysLeanExtract.TypeRewriter
import PhysLeanExtract.JsonEmitter

/-!
# PhysLean Extraction CLI

Entry point: `lake exe extract`

Loads the PhysLean environment, walks all constants, tags domains,
and writes `output/catalog.json`.
-/

open Lean PhysLeanExtract

/-- Main entry point for the extraction tool. -/
def main : IO Unit := do
  IO.println "PhysLean Extraction Tool"
  IO.println "========================"
  IO.println ""

  -- Initialize search paths for .olean files
  Lean.initSearchPath (← Lean.findSysroot)

  IO.println "Loading PhysLean environment (this may take a moment)..."

  -- Load PhysLean environment (reads compiled .olean files)
  let env ← Lean.importModules #[{ module := `PhysLean }] {} 0

  IO.println s!"Environment loaded: {env.constants.map₁.size} constants"

  -- Set up Core/Meta context with the loaded environment
  let coreCtx : Lean.Core.Context := {
    fileName := "<extract>"
    fileMap := .ofString ""
  }
  let coreState : Lean.Core.State := { env }

  -- Run walker in MetaM to extract theorems and types
  IO.println "Walking environment for theorems..."
  let ((theorems, types), _) ← (do
    let theorems ← walkTheorems
    let types ← walkTypes
    pure (theorems, types)
    : Meta.MetaM _).run'.toIO coreCtx coreState

  IO.println s!"Found {theorems.size} theorems/definitions"
  IO.println s!"Found {types.size} types/structures"


  -- Apply type rewriting to classify signatures
  let theorems := theorems.map fun t =>
    let (rewritten, canReax) := rewriteTypeSignature t.typeSignature
    { t with
      typeSignature := rewritten
      rawSignature := t.rawSignature  -- Keep original
      canReaxiomatize := canReax }

  let reaxCount := theorems.filter (·.canReaxiomatize) |>.size
  IO.println s!"  {reaxCount} can be re-axiomatized"
  IO.println s!"  {theorems.size - reaxCount} have complex signatures (skipped)"

  -- Generate catalog JSON
  let catalog := renderCatalog theorems types "v4.26.0" "4.26.0"

  -- Write to output/catalog.json
  let outputPath := "output/catalog.json"
  -- Ensure output directory exists
  IO.FS.createDirAll "output"
  IO.FS.writeFile outputPath catalog
  IO.println s!"Wrote catalog to {outputPath}"
  IO.println "Done."
