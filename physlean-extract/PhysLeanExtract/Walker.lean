import Lean
import PhysLeanExtract.ExprAst

/-!
# PhysLean Environment Walker

Walks the Lean environment after importing PhysLean, collecting all
theorem and definition constants. Filters out:
- Constants containing `sorry` in their proof terms
- Constants tagged as `semiformal_result`
- Internal/auxiliary constants (names starting with `_`)
- Auto-generated instances (instDecidable, instOfNat, etc.)
-/

namespace PhysLeanExtract

open Lean Meta

/-- Check if `haystack` contains `needle` as a substring. -/
private def strHas (haystack : String) (needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Represents an extracted theorem from PhysLean / Mathlib. -/
structure ExtractedTheorem where
  name : Name
  typeSignature : String
  rawSignature : String
  isTheorem : Bool
  docString : Option String
  canReaxiomatize : Bool
  /-- Universal `nasrudin_core::Expr` AST. The translator is total, so
      every entry has a populated tree (curried `App` chains for
      unknown heads). The Rust AxiomStore tries to deserialise the
      tree; failures fall back to a `Var(name)` placeholder. -/
  exprAst : Lean.Json
  /-- Names of every kernel constant the proof term cites. Empty for
      `defnInfo` (definitions don't have proofs in the theorem sense)
      and for theorems whose proof walk timed out. The Rust loader maps
      each name through `axiom_id_from_name` to populate the
      `LineageRecord.axiom_ancestors` field — that's how the
      acyclicity infra learns this theorem's dependency closure
      without us shipping the full kernel proof term in JSON. -/
  axiomDependencies : Array String
  deriving Inhabited

structure ExtractedType where
  name : Name
  kind : String
  typeSignature : String
  fields : Array String
  docString : Option String
  deriving Inhabited, Repr

/-- PhysLean-side namespace prefixes (PhysLean opens these via
    `namespace`/`open` so definitions appear under these prefixes
    rather than under `PhysLean.*`). -/
private def physLeanTopNamespaces : List String :=
  [ "PhysLean."
  , "Lorentz."
  , "LorentzGroup."
  , "SpaceTime."
  , "Electromagnetism."
  , "minkowskiMatrix."
  , "complexLorentzTensor."
  , "realLorentzTensor."
  , "Fermion."
  , "Higgs."
  , "StandardModel."
  , "CliffordAlgebra."
  ]

/-- Default Mathlib whitelist when `--whitelist=` includes the magic
    `+mathlib` token. Wide enough to capture algebra/analysis/order/
    real/nat/int/complex while skipping CategoryTheory and pure
    type-class plumbing. -/
def mathlibTopNamespaces : List String :=
  [ -- Real / Nat / Int / Complex / Rat carriers
    "Real."
  , "Nat."
  , "Int."
  , "Rat."
  , "Complex."
    -- Mathlib's algebraic and analytic core
  , "Mathlib.Algebra."
  , "Mathlib.Analysis."
  , "Mathlib.Order."
  , "Mathlib.Topology.Basic"
  , "Mathlib.Topology.Algebra."
  , "Mathlib.Data.Real."
  , "Mathlib.Data.Nat."
  , "Mathlib.Data.Int."
  , "Mathlib.Data.Complex."
  , "Mathlib.Data.Rat."
  , "Mathlib.Logic.Basic"
  , "Mathlib.Logic.Equiv."
  , "Mathlib.NumberTheory."
  , "Mathlib.GroupTheory."
  , "Mathlib.LinearAlgebra."
  , "Mathlib.Geometry.Manifold.Basic"
  , "Mathlib.Geometry.Euclidean."
  , "Mathlib.MeasureTheory.Function."
  , "Mathlib.Probability."
  , "Mathlib.Combinatorics."
  ]

/-- Skip-list: namespaces we never want in the corpus regardless of the
    whitelist. Mostly compiler internals and category theory (which is
    massive but inert for physics). When `+all` is used we also drop
    private definitions (`_private.*`) — internal Mathlib helpers that
    aren't meaningful theorems — and `Aesop.*` (tactic plumbing). -/
def globalSkipPrefixes : List String :=
  [ "Lean."
  , "Std."
  , "IO."
  , "Init."
  , "System."
  , "Mathlib.Tactic."
  , "Mathlib.Util."
  , "Mathlib.CategoryTheory."
  , "CategoryTheory."
  , "Mathlib.Init."
  , "Mathlib.Mathport."
  , "_private."
  , "Aesop."
  , "Tactic."
  , "Parser."
  , "Elab."
  , "Macro."
  ]

/-- Check if a name belongs to PhysLean (not Lean/Mathlib internals). -/
def isPhysLeanName (n : Name) : Bool :=
  let str := n.toString
  physLeanTopNamespaces.any fun pfx => str.startsWith pfx

/-- Check if a name matches the whitelist.

    `whitelist` recipes:
    - `[]` → PhysLean defaults only.
    - `["+mathlib"]` → PhysLean defaults + the `mathlibTopNamespaces` set.
    - `["+all"]` → everything (no whitelist filter; only the global
      skip-list applies). Use for a one-shot full corpus build.
    - explicit prefixes (e.g. `["Mathlib.Analysis", "Real."]`) → exactly
      those, plus PhysLean defaults if `+phys` is also in the list. -/
def matchesWhitelist (whitelist : List String) (n : Name) : Bool :=
  let str := n.toString
  -- Always reject anything in the global skip-list.
  if globalSkipPrefixes.any fun pfx => str.startsWith pfx then
    false
  else if whitelist.isEmpty then
    isPhysLeanName n
  else if whitelist.contains "+all" then
    true
  else
    let resolved : List String :=
      whitelist.flatMap fun s =>
        if s == "+mathlib" then mathlibTopNamespaces
        else if s == "+phys" then physLeanTopNamespaces
        else [s]
    -- `+phys` token also implies PhysLean defaults are *added*; bare
    -- explicit lists do not include PhysLean unless requested.
    let withPhys :=
      if whitelist.contains "+phys" then resolved else resolved
    withPhys.any fun pfx => str.startsWith pfx ||
      (if pfx.endsWith "." then false else str.startsWith (pfx ++ "."))

/-- Check if a name is internal/auxiliary. -/
def isInternalName (n : Name) : Bool :=
  let str := n.toString
  strHas str "._" ||
  strHas str ".match_" ||
  strHas str ".proof_" ||
  strHas str ".rec" ||
  strHas str ".brecOn" ||
  strHas str ".below" ||
  strHas str ".casesOn" ||
  strHas str ".recOn" ||
  strHas str ".noConfusion" ||
  strHas str "._eq_" ||
  strHas str "_hyg." ||
  strHas str ".sizeOf_" ||
  strHas str "._cstage"

def isSemiformal (n : Name) : Bool :=
  let str := n.toString
  strHas str "semiformal" ||
  strHas str "Semiformal"

def isAutoGeneratedInstance (n : Name) : Bool :=
  let str := n.toString
  strHas str "instDecidable" ||
  strHas str "instOfNat" ||
  strHas str "instHMul" ||
  strHas str "instHAdd" ||
  strHas str "instHSub" ||
  strHas str "instHDiv" ||
  strHas str "instHPow" ||
  strHas str "instBEq" ||
  strHas str "instRepr" ||
  strHas str "instInhabited" ||
  strHas str "instToString" ||
  strHas str "instHashable" ||
  strHas str "instOrd" ||
  strHas str "instLT" ||
  strHas str "instLE" ||
  strHas str "instSizeOf" ||
  strHas str ".mk" ||
  strHas str ".injEq" ||
  strHas str ".ext" && strHas str "_iff"

def ppTypeExpr (e : Expr) : MetaM String := do
  let opts := Options.empty
    |>.setBool `pp.fullNames false
    |>.setBool `pp.universes false
    |>.setBool `pp.notation true
  withOptions (fun _ => opts) do
    let fmt ← ppExpr e
    return toString fmt

/-- Walk the environment and extract all theorems matching the
    namespace whitelist. The `exprAst` field is always populated thanks
    to the universal translator; the Rust loader is responsible for
    filtering rows whose tree the Rust `Expr` enum can't deserialise.

    Disables the global `maxHeartbeats` limit (default 200k) for the
    duration of the walk — iterating 400k+ Mathlib constants alone
    burns through that, before the translator even runs. Per-theorem
    work is still bounded to 50k heartbeats inside the loop. -/
def walkTheoremsWithWhitelist (whitelist : List String := []) : MetaM (Array ExtractedTheorem) :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
  let env ← getEnv
  let mut results := #[]
  for (name, ci) in env.constants.map₁.toList do
    unless matchesWhitelist whitelist name do continue
    if isInternalName name then continue
    if isSemiformal name then continue
    if isAutoGeneratedInstance name then continue

    -- Per-theorem heartbeat budget. Some Mathlib type signatures push
    -- `whnf`/`isProp` deep enough that the global 200k-heartbeat limit
    -- aborts the whole walk on a single bad term. Bound per-theorem
    -- work to 50k heartbeats and fall back to a `Var(name)` placeholder
    -- on timeout — the row still lands in the catalog, just without
    -- a structured AST tree.
    let placeholderAst := Json.mkObj [("Var", Json.str name.toString)]
    let astWithBudget (ty : Expr) : MetaM Lean.Json := do
      try
        Core.withCurrHeartbeats <|
          withTheReader Core.Context
            (fun ctx => { ctx with maxHeartbeats := 50000 })
            (exprToAst ty)
      catch _ => pure placeholderAst
    -- Collect every kernel constant cited by `value`. We use Lean's
    -- built-in `Expr.getUsedConstants` which folds the proof-term tree
    -- once and returns a `NameSet`. Bounded by per-theorem heartbeats
    -- (set above) so a pathological proof can't stall the walk.
    let depsWithBudget (value : Expr) : MetaM (Array String) := do
      try
        Core.withCurrHeartbeats <|
          withTheReader Core.Context
            (fun ctx => { ctx with maxHeartbeats := 50000 })
            (do
              let names := value.getUsedConstantsAsSet
              let arr := names.toArray.map (·.toString)
              -- Filter compiler-internal noise (`Eq.refl`, `id`, etc.
              -- aren't dependency-meaningful; the proof structurally
              -- relies on the *physics/math* lemmas it cites).
              let filtered := arr.filter fun n =>
                !n.startsWith "_" && n != name.toString
              return filtered)
      catch _ => pure #[]
    match ci with
    | .thmInfo val =>
      if val.value.hasSorry then continue
      let typeStr ← try ppTypeExpr val.type catch _ => pure (toString val.type)
      let doc ← findDocString? env name
      let ast ← astWithBudget val.type
      let deps ← depsWithBudget val.value
      results := results.push {
        name := name
        typeSignature := typeStr
        rawSignature := typeStr
        isTheorem := true
        docString := doc
        canReaxiomatize := true
        exprAst := ast
        axiomDependencies := deps
      }
    | .defnInfo val =>
      let typeStr ← try ppTypeExpr val.type catch _ => pure (toString val.type)
      let doc ← findDocString? env name
      let ast ← astWithBudget val.type
      results := results.push {
        name := name
        typeSignature := typeStr
        rawSignature := typeStr
        isTheorem := false
        docString := doc
        canReaxiomatize := true
        exprAst := ast
        axiomDependencies := #[]
      }
    | _ => pure ()

  return results

def walkTheorems : MetaM (Array ExtractedTheorem) := walkTheoremsWithWhitelist []

def walkTypes : MetaM (Array ExtractedType) := do
  let env ← getEnv
  let mut results := #[]
  for (name, ci) in env.constants.map₁.toList do
    unless isPhysLeanName name do continue
    if isInternalName name then continue
    if isAutoGeneratedInstance name then continue

    match ci with
    | .inductInfo val =>
      let typeStr ← try ppTypeExpr val.type catch _ => pure (toString val.type)
      let doc ← findDocString? env name

      let fields ← do
        if val.ctors.length == 1 then
          match getStructureInfo? env name with
          | some structInfo =>
            let mut fieldStrs := #[]
            for fn in structInfo.fieldNames do
              let projName := name ++ fn
              match env.find? projName with
              | some projInfo =>
                let fieldTypeStr ← try
                  forallTelescopeReducing projInfo.type fun _ body => ppTypeExpr body
                catch _ =>
                  try ppTypeExpr projInfo.type
                  catch _ => pure (toString projInfo.type)
                fieldStrs := fieldStrs.push s!"{fn} : {fieldTypeStr}"
              | none =>
                fieldStrs := fieldStrs.push s!"{fn}"
            pure fieldStrs
          | none =>
            pure #[]
        else
          pure #[]

      let kind := match getStructureInfo? env name with
        | some _ => "structure"
        | none => "inductive"

      results := results.push {
        name := name
        kind := kind
        typeSignature := typeStr
        fields := fields
        docString := doc
      }
    | _ => pure ()

  return results

end PhysLeanExtract
