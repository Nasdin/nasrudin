import Lean
import PhysLeanExtract.Walker
import PhysLeanExtract.DomainTagger

/-!
# JSON Emitter

Serializes extracted theorems, types, and constants to the catalog JSON format
consumed by the Rust importer crate.
-/

namespace PhysLeanExtract

open Lean

private def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\"
   |>.replace "\"" "\\\""
   |>.replace "\n" "\\n"
   |>.replace "\r" "\\r"
   |>.replace "\t" "\\t"

private def jsonString (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonOptString : Option String → String
  | some s => jsonString s
  | none => "null"

private def jsonBool (b : Bool) : String :=
  if b then "true" else "false"

/-- Render a theorem entry as JSON. The `expr_ast` field is always
    populated (the universal translator never fails). The
    `axiom_dependencies` field lists every kernel constant the proof
    term cites — empty for definitions and for theorems whose
    proof-walk timed out. -/
def theoremToJson (t : ExtractedTheorem) (domain : PhysDomain) : String :=
  let shortName := t.name.toString.replace "PhysLean." ""
    |>.replace "." "_"
    |>.toLower
  let depEntries := t.axiomDependencies.toList.map jsonString
  let depsStr := ", ".intercalate depEntries
  "{" ++
    "\n    \"name\": " ++ jsonString shortName ++
    ",\n    \"physlean_name\": " ++ jsonString t.name.toString ++
    ",\n    \"domain\": " ++ jsonString domain.toJsonString ++
    ",\n    \"type_signature\": " ++ jsonString t.typeSignature ++
    ",\n    \"raw_signature\": " ++ jsonString t.rawSignature ++
    ",\n    \"can_reaxiomatize\": " ++ jsonBool t.canReaxiomatize ++
    ",\n    \"source\": \"physlean\"" ++
    ",\n    \"doc_string\": " ++ jsonOptString t.docString ++
    ",\n    \"expr_ast\": " ++ t.exprAst.compress ++
    ",\n    \"axiom_dependencies\": [" ++ depsStr ++ "]" ++
    "\n  }"

def typeToJson (t : ExtractedType) : String :=
  let fieldArr := t.fields.toList.map jsonString
  let fieldsStr := ", ".intercalate fieldArr
  let typeName := match t.name.toString.splitOn "." |>.getLast? with
    | some n => n
    | none => t.name.toString
  "{" ++
    "\n    \"name\": " ++ jsonString typeName ++
    ",\n    \"physlean_name\": " ++ jsonString t.name.toString ++
    ",\n    \"kind\": " ++ jsonString t.kind ++
    ",\n    \"type_signature\": " ++ jsonString t.typeSignature ++
    ",\n    \"fields\": [" ++ fieldsStr ++ "]" ++
    ",\n    \"doc_string\": " ++ jsonOptString t.docString ++
    "\n  }"

/-- Render the full catalog JSON. **No domain filter** — every walked
    theorem flows through. Theorems whose namespace doesn't map to a
    known `PhysDomain` get `domain = "Unknown"`; the Rust loader maps
    that to `Domain::PureMath` and registers them anyway. -/
def renderCatalog
    (theorems : Array ExtractedTheorem)
    (types : Array ExtractedType)
    (physleanVersion : String)
    (leanVersion : String) : String :=
  let thmEntries := theorems.toList.map fun t =>
    let domain := tagDomain t.name
    theoremToJson t domain
  let thmsStr := ",\n    ".intercalate thmEntries

  -- Types still filter Unknown — they're decorative metadata for the
  -- frontend, not GA building blocks.
  let typeEntries := types.toList.filterMap fun t =>
    let domain := tagDomain t.name
    if domain == .Unknown then none
    else some (typeToJson t)
  let typesStr := ",\n    ".intercalate typeEntries

  let domainImports := [
    ("ClassicalMechanics", "PhysicsGenerator.Generated.Mechanics"),
    ("SpecialRelativity", "PhysicsGenerator.Generated.SpecialRelativity"),
    ("Electromagnetism", "PhysicsGenerator.Generated.Electromagnetism"),
    ("QuantumMechanics", "PhysicsGenerator.Generated.QuantumMechanics"),
    ("Thermodynamics", "PhysicsGenerator.Generated.Thermodynamics")
  ]
  let importsEntries := domainImports.map fun (k, v) =>
    "    " ++ jsonString k ++ ": " ++ jsonString v
  let importsStr := ",\n".intercalate importsEntries

  "{\n" ++
  "  \"physlean_version\": " ++ jsonString physleanVersion ++ ",\n" ++
  "  \"lean_version\": " ++ jsonString leanVersion ++ ",\n" ++
  "  \"theorems\": [\n    " ++ thmsStr ++ "\n  ],\n" ++
  "  \"types\": [\n    " ++ typesStr ++ "\n  ],\n" ++
  "  \"constants\": [\n" ++
  "    {\"name\": \"c\", \"type\": \"\\u211d\", \"positivity\": \"0 < c\"},\n" ++
  "    {\"name\": \"G\", \"type\": \"\\u211d\", \"positivity\": \"0 < G\"},\n" ++
  "    {\"name\": \"hbar\", \"type\": \"\\u211d\", \"positivity\": \"0 < hbar\"},\n" ++
  "    {\"name\": \"k_B\", \"type\": \"\\u211d\", \"positivity\": \"0 < k_B\"}\n" ++
  "  ],\n" ++
  "  \"domain_imports\": {\n" ++ importsStr ++ "\n  }\n" ++
  "}"

end PhysLeanExtract
