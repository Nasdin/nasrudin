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

/-- Escape a string for JSON output. -/
private def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\"
   |>.replace "\"" "\\\""
   |>.replace "\n" "\\n"
   |>.replace "\r" "\\r"
   |>.replace "\t" "\\t"

/-- Render a JSON string value. -/
private def jsonString (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

/-- Render an optional JSON string value. -/
private def jsonOptString : Option String → String
  | some s => jsonString s
  | none => "null"

/-- Render a boolean as JSON. -/
private def jsonBool (b : Bool) : String :=
  if b then "true" else "false"

/-- Render a theorem entry as JSON. -/
def theoremToJson (t : ExtractedTheorem) (domain : PhysDomain) : String :=
  let shortName := t.name.toString.replace "PhysLean." ""
    |>.replace "." "_"
    |>.toLower
  "{" ++
    "\n    \"name\": " ++ jsonString shortName ++
    ",\n    \"physlean_name\": " ++ jsonString t.name.toString ++
    ",\n    \"domain\": " ++ jsonString domain.toJsonString ++
    ",\n    \"type_signature\": " ++ jsonString t.typeSignature ++
    ",\n    \"raw_signature\": " ++ jsonString t.rawSignature ++
    ",\n    \"can_reaxiomatize\": " ++ jsonBool t.canReaxiomatize ++
    ",\n    \"source\": \"physlean\"" ++
    ",\n    \"doc_string\": " ++ jsonOptString t.docString ++
    "\n  }"

/-- Render a type entry as JSON. -/
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

/-- Render the full catalog JSON. -/
def renderCatalog
    (theorems : Array ExtractedTheorem)
    (types : Array ExtractedType)
    (physleanVersion : String)
    (leanVersion : String) : String :=
  -- Build theorem entries with domain tags
  let thmEntries := theorems.toList.filterMap fun t =>
    let domain := tagDomain t.name
    if domain == .Unknown then none
    else some (theoremToJson t domain)
  let thmsStr := ",\n    ".intercalate thmEntries

  -- Build type entries (filtered to known domains)
  let typeEntries := types.toList.filterMap fun t =>
    let domain := tagDomain t.name
    if domain == .Unknown then none
    else some (typeToJson t)
  let typesStr := ",\n    ".intercalate typeEntries

  -- Build domain_imports map
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
