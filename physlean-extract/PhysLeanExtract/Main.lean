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

/-- Main entry point for the extraction tool.
    `lake exe extract` walks PhysLean only.
    `lake exe extract --whitelist=Mathlib.Algebra,Real.,Mathlib.Analysis.SpecialFunctions.Pow.Real`
       walks the listed namespace prefixes (in *addition* to PhysLean
       defaults if `+phys` is in the list, otherwise *replaces* them).
    `lake exe extract --output=output/math_corpus.json` redirects output. -/
def main (args : List String) : IO Unit := do
  IO.println "PhysLean Extraction Tool"
  IO.println "========================"
  IO.println ""

  -- Parse CLI flags. We support:
  --   --whitelist=A,B,C   comma-separated namespace prefixes
  --   --output=path       output file (default output/catalog.json)
  let getFlag (key : String) : Option String :=
    args.findSome? fun a =>
      let p := key ++ "="
      if a.startsWith p then some (a.drop p.length) else none
  let whitelistStr := getFlag "--whitelist" |>.getD ""
  let outputPath := getFlag "--output" |>.getD "output/catalog.json"
  let whitelist : List String :=
    if whitelistStr.isEmpty then []
    else whitelistStr.splitOn ","
      |>.map String.trim |>.filter (fun s => !s.isEmpty)
  if whitelist.isEmpty then
    IO.println "Whitelist: PhysLean defaults (no --whitelist given)"
  else
    IO.println s!"Whitelist: {whitelist}"

  -- Initialize search paths for .olean files
  Lean.initSearchPath (← Lean.findSysroot)

  IO.println "Loading environment (this may take a moment)..."
  -- Always import PhysLean (which transitively imports Mathlib). When
  -- only Mathlib namespaces are in the whitelist, PhysLean's load is
  -- harmless overhead — the walker just won't emit PhysLean constants.
  let env ← Lean.importModules #[{ module := `PhysLean }] {} 0

  IO.println s!"Environment loaded: {env.constants.map₁.size} constants"

  -- Set up Core/Meta context with the loaded environment.
  --
  -- Disable the global `maxHeartbeats` limit (default 200k) for the
  -- whole walk: iterating 400k+ Mathlib constants plus all the
  -- per-constant `whnf`/`isProp`/`getFunInfo` calls in the translator
  -- burns through that many times over. This is a one-shot extraction
  -- run, not interactive elaboration — there's no reason to bound it.
  let coreCtx : Lean.Core.Context := {
    fileName := "<extract>"
    fileMap := .ofString ""
    maxHeartbeats := 0
  }
  let coreState : Lean.Core.State := { env }

  -- Run walker in MetaM to extract theorems and types
  IO.println "Walking environment for theorems..."
  let ((theorems, types), _) ← (do
    let theorems ← walkTheoremsWithWhitelist whitelist
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

  -- Coverage report: every theorem has a populated expr_ast (the
  -- universal translator is total). Count the rows whose tree is
  -- richer than just `Var(name)` — those are the ones the GA can
  -- actually mutate. Bare `Var` rows are inert placeholders.
  let astRich := theorems.filter (fun t =>
    let s := t.exprAst.compress
    !s.startsWith "{\"Var\"") |>.size
  IO.println s!"  {astRich} / {theorems.size} theorems have a structured (non-Var-only) expr_ast"

  -- Ensure parent directory exists (handles output/ subdir case).
  let parts := outputPath.splitOn "/"
  if parts.length > 1 then
    let dir := "/".intercalate (parts.dropLast)
    IO.FS.createDirAll dir
  IO.FS.writeFile outputPath catalog
  IO.println s!"Wrote catalog to {outputPath}"
  IO.println "Done."
