/-!
# JSON Emitter

Serializes extracted theorems, types, and constants to the catalog JSON format
consumed by the Rust importer crate.
-/

import Lean
import PhysLeanExtract.Walker
import PhysLeanExtract.DomainTagger

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
  s!"\"{ jsonEscape s }\""

/-- Render an optional JSON string value. -/
private def jsonOptString : Option String → String
  | some s => jsonString s
  | none => "null"

/-- Render a theorem entry as JSON. -/
def theoremToJson (t : ExtractedTheorem) (domain : PhysDomain) : String :=
  let shortName := t.name.toString.replace "PhysLean." ""
    |>.replace "." "_"
    |>.toLower
  s!"\{
    \"name\": {jsonString shortName},
    \"physlean_name\": {jsonString t.name.toString},
    \"domain\": {jsonString domain.toJsonString},
    \"type_signature\": {jsonString t.typeSignature},
    \"source\": \"physlean\",
    \"doc_string\": {jsonOptString t.docString}
  \}"

/-- Render a type entry as JSON. -/
def typeToJson (t : ExtractedType) : String :=
  let fieldArr := t.fields.toList.map jsonString
  let fieldsStr := ", ".intercalate fieldArr
  s!"\{
    \"name\": {jsonString t.name.getString!},
    \"physlean_name\": {jsonString t.name.toString},
    \"kind\": {jsonString t.kind},
    \"type_signature\": {jsonString t.typeSignature},
    \"fields\": [{fieldsStr}]
  \}"

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
    s!"    {jsonString k}: {jsonString v}"
  let importsStr := ",\n".intercalate importsEntries

  s!"\{
  \"physlean_version\": {jsonString physleanVersion},
  \"lean_version\": {jsonString leanVersion},
  \"theorems\": [
    {thmsStr}
  ],
  \"types\": [
    {typesStr}
  ],
  \"constants\": [
    \{
      \"name\": \"c\",
      \"type\": \"ℝ\",
      \"positivity\": \"0 < c\"
    \},
    \{
      \"name\": \"G\",
      \"type\": \"ℝ\",
      \"positivity\": \"0 < G\"
    \},
    \{
      \"name\": \"hbar\",
      \"type\": \"ℝ\",
      \"positivity\": \"0 < hbar\"
    \},
    \{
      \"name\": \"k_B\",
      \"type\": \"ℝ\",
      \"positivity\": \"0 < k_B\"
    \}
  ],
  \"domain_imports\": \{
{importsStr}
  \}
\}"

end PhysLeanExtract
