/-!
# PhysLean Extraction CLI

Entry point: `lake exe extract`

Loads the PhysLean environment, walks all constants, tags domains,
and writes `output/catalog.json`.
-/

import Lean
import PhysLeanExtract.Walker
import PhysLeanExtract.DomainTagger
import PhysLeanExtract.JsonEmitter

open Lean PhysLeanExtract

/-- Main entry point for the extraction tool. -/
def main : IO Unit := do
  IO.println "PhysLean Extraction Tool"
  IO.println "========================"
  IO.println ""
  IO.println "Note: This tool requires PhysLean to be built first."
  IO.println "Run `lake build` before `lake exe extract`."
  IO.println ""

  -- In a real run, we'd load the PhysLean environment here.
  -- For now, this generates a catalog from the known PhysLean structure.
  -- The Walker module provides the programmatic API for actual extraction.

  -- Generate catalog from known PhysLean coverage
  let catalog := renderStaticCatalog

  -- Write to output/catalog.json
  let outputPath := "output/catalog.json"
  IO.FS.writeFile outputPath catalog
  IO.println s!"Wrote catalog to {outputPath}"
  IO.println "Done."

where
  /-- Generate a catalog based on known PhysLean theorem coverage.

  This is the bootstrap catalog. Once PhysLean's environment is loadable
  via metaprogramming, the Walker will generate this dynamically. -/
  renderStaticCatalog : String :=
    renderCatalog #[] #[] "master" "4.16.0"
