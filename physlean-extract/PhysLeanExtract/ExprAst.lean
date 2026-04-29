import Lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lean → nasrudin_core::Expr AST translator (universal)

Walks a Lean `Expr` tree and emits a JSON object whose shape matches the
`nasrudin_core::Expr` enum (engine/crates/core/src/expr.rs).

This translator is **total**: every Lean expression yields some structured
tree. Known heads (`HAdd/Eq/Le/Iff/Real.exp/...`) get specialised
`BinOp`/`UnOp`/`Const` nodes; everything else lands as a curried `App`
chain over a `Var(headName)`. Hypothesis-shaped `forallE` (Prop → Prop,
non-dependent) becomes `BinOp(Implies, …)`; dependent foralls become
`Pi(name, type, body)`; `lam` becomes `Lam(name, type, body)`.

Wire shape (matches Rust's externally-tagged serde derive):

  Var(String)                    → {"Var": "E"}
  Const(PhysConst)               → {"Const": "SpeedOfLight"}
  Lit(num, den)                  → {"Lit": [num, den]}
  App(lhs, rhs)                  → {"App": [<lhs>, <rhs>]}
  Lam(name, ty, body)            → {"Lam": ["x", <ty>, <body>]}
  Pi(name, ty, body)             → {"Pi":  ["x", <ty>, <body>]}
  BinOp(op, lhs, rhs)            → {"BinOp": ["Op", <lhs>, <rhs>]}
  UnOp(op, arg)                  → {"UnOp":  ["Op", <arg>]}

The Rust `Expr` enum (BinOp/UnOp variants) is the source of truth for
the operator name strings emitted here.
-/

namespace PhysLeanExtract

open Lean Meta

/-- A handful of named physics constants we recognise on the LHS/RHS of
    Lean equations. Names match `nasrudin_core::PhysConst`. -/
private def physConstName : Name → Option String
  | `PhysLean.SpeedOfLight        => some "SpeedOfLight"
  | `PhysLean.PhysicalConstants.c => some "SpeedOfLight"
  | `PhysLean.PhysicalConstants.G => some "GravConst"
  | `PhysLean.PhysicalConstants.hbar => some "ReducedPlanck"
  | `PhysLean.PhysicalConstants.k_B => some "Boltzmann"
  | `Real.pi => some "Pi"
  | _ => none

/-- Pull out a Nat literal from a `Lean.Expr` if it has one. -/
private partial def asNatLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) _) n) _ => asNatLit? n
  | _ => none

/-- Recognise the subset of Lean `Expr` heads we translate as binary
    operators. Names match the Rust `BinOp` enum variants verbatim. -/
private def binOpFor : Name → Option String
  | ``HAdd.hAdd => some "Add"
  | ``HSub.hSub => some "Sub"
  | ``HMul.hMul => some "Mul"
  | ``HDiv.hDiv => some "Div"
  | ``HPow.hPow => some "Pow"
  | ``Eq        => some "Eq"
  | ``Ne        => some "Ne"
  | ``Iff       => some "Iff"
  | ``And       => some "And"
  | ``Or        => some "Or"
  | ``LE.le     => some "Le"
  | ``LT.lt     => some "Lt"
  | ``GE.ge     => some "Ge"
  | ``GT.gt     => some "Gt"
  | _           => none

/-- Recognise unary operators. Names match Rust `UnOp` variants. -/
private def unOpFor : Name → Option String
  | ``Neg.neg     => some "Neg"
  | ``Real.sqrt   => some "Sqrt"
  | ``Real.exp    => some "Exp"
  | ``Real.log    => some "Log"
  | ``Real.sin    => some "Sin"
  | ``Real.cos    => some "Cos"
  | ``Real.tan    => some "Tan"
  | ``abs         => some "Abs"
  | _             => none

/-- Build a `Json` for a literal natural number. -/
private def jsonNat (n : Nat) : Json :=
  Json.num (JsonNumber.fromInt (Int.ofNat n))

/-- Build the `Lit` wrapper (rational with denominator 1). -/
private def litJson (n : Nat) : Json :=
  Json.mkObj [("Lit", Json.arr #[jsonNat n, jsonNat 1])]

/-- Build a `Var` wrapper. -/
private def varJson (s : String) : Json :=
  Json.mkObj [("Var", Json.str s)]

/-- Build an `App(f, x)` Json node. -/
private def appJson (f x : Json) : Json :=
  Json.mkObj [("App", Json.arr #[f, x])]

/-- Curry an n-ary application head over a list of arg JSONs. -/
private def appChain (head : Json) (args : Array Json) : Json :=
  args.foldl (init := head) fun acc a => appJson acc a

/-- Try to pull `BinderInfo`s for the head's declared parameters via
    `getFunInfo`. Returns the array of `ParamInfo`, or `#[]` if anything
    goes wrong (e.g. higher-order or partially-applied). -/
private def tryFunInfo (head : Expr) : MetaM (Array Lean.Meta.ParamInfo) := do
  try
    let info ← getFunInfo head
    return info.paramInfo
  catch _ => return #[]

/-- Drop type-class / implicit / strict-implicit / inst-implicit args by
    consulting `getFunInfo` on the head. Args at default-binder positions
    are kept; everything else is dropped. If `getFunInfo` fails we keep
    all args (over-emit beats under-emit). -/
private def explicitArgs (head : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let info ← tryFunInfo head
  if info.isEmpty then return args
  let mut out := #[]
  for i in [0:args.size] do
    if h : i < info.size then
      let p := info[i]'h
      if p.binderInfo == BinderInfo.default then
        out := out.push args[i]!
    else
      -- Past the declared params (higher-order return) → keep.
      out := out.push args[i]!
  return out

/-- Translate a Lean `Expr` into a `Json` tree matching `nasrudin_core::Expr`.

    **Total**: returns a structured tree for every input. Known heads
    specialise into `BinOp`/`UnOp`/`Const`/`Lit`; unknown heads fall
    back to `App(Var headName, …)` curried chains. Hypothesis-shaped
    foralls become `Implies`; dependent foralls become `Pi`. -/
partial def exprToAst (e : Expr) : MetaM Json := do
  match e with
  -- Strip metadata wrappers transparently.
  | .mdata _ inner => exprToAst inner

  -- Literals -----------------------------------------------------------
  | .lit (.natVal n) => return litJson n
  | .lit (.strVal s) => return varJson s!"<str:{s}>"

  -- Bound variables shouldn't appear after telescope, but be defensive.
  | .bvar i => return varJson s!"_b{i}"

  -- Sort / metavariable → opaque carrier.
  | .sort _ => return varJson "<sort>"
  | .mvar id => return varJson s!"?m.{id.name}"

  -- Projection: emit as `Var "Struct.proj"` applied to the struct expr.
  | .proj structName idx struct => do
      let inner ← exprToAst struct
      return appJson (varJson s!"{structName}.{idx}") inner

  -- Free variables (after entering binders) ----------------------------
  | .fvar fvarId => do
      let decl ← fvarId.getDecl
      return varJson decl.userName.toString

  -- Named constants ----------------------------------------------------
  | .const name _ => do
      match physConstName name with
      | some pc => return Json.mkObj [("Const", Json.str pc)]
      | none    => return varJson name.toString

  -- Universal binders --------------------------------------------------
  -- Non-dependent forall = implication. If the binder type is a `Prop`
  -- and doesn't appear free in the body, emit `BinOp(Implies, hyp, body)`.
  -- Otherwise emit `Pi(name, ty, body)` with the binder introduced as
  -- a free variable so its name appears in `Var(...)`.
  | .forallE _binderName binderType body _ => do
      let isProp ← try Meta.isProp binderType catch _ => pure false
      let dependent := body.hasLooseBVar 0
      if isProp && !dependent then
        let lhs ← exprToAst binderType
        let rhs ← exprToAst (body.lowerLooseBVars 1 1)
        return Json.mkObj [("BinOp", Json.arr #[Json.str "Implies", lhs, rhs])]
      else
        forallBoundedTelescope e (some 1) fun xs body' => do
          let x := xs[0]!
          let xDecl ← x.fvarId!.getDecl
          let tyJson ← exprToAst xDecl.type
          let bodyJson ← exprToAst body'
          return Json.mkObj [("Pi", Json.arr #[Json.str xDecl.userName.toString, tyJson, bodyJson])]

  -- Lambdas ------------------------------------------------------------
  | .lam _binderName _ _ _ => do
      lambdaBoundedTelescope e 1 fun xs body' => do
        let x := xs[0]!
        let xDecl ← x.fvarId!.getDecl
        let tyJson ← exprToAst xDecl.type
        let bodyJson ← exprToAst body'
        return Json.mkObj [("Lam", Json.arr #[Json.str xDecl.userName.toString, tyJson, bodyJson])]

  -- Let-bindings: substitute (β-reduce) and recurse. Drops the binding
  -- name but preserves structure — the corpus rarely needs the let-name.
  | .letE _ _ val body _ => do
      exprToAst (body.instantiate1 val)

  -- Application chains -------------------------------------------------
  | .app _ _ => do
      let head := e.getAppFn
      let args := e.getAppArgs
      match head with
      | .const name _ =>
          -- BinOp: take the last two args (typeclass carriers come first).
          if let some op := binOpFor name then
            if args.size >= 2 then
              let lhs ← exprToAst args[args.size - 2]!
              let rhs ← exprToAst args[args.size - 1]!
              return Json.mkObj [("BinOp", Json.arr #[Json.str op, lhs, rhs])]
            else
              -- Partially-applied operator — fall through to App chain.
              let explicit ← explicitArgs head args
              let explicitJ ← explicit.mapM exprToAst
              return appChain (varJson name.toString) explicitJ
          else if let some op := unOpFor name then
            if args.size >= 1 then
              let inner ← exprToAst args[args.size - 1]!
              return Json.mkObj [("UnOp", Json.arr #[Json.str op, inner])]
            else
              return varJson name.toString
          else if name == ``OfNat.ofNat then
            match asNatLit? e with
            | some n => return litJson n
            | none =>
                let explicit ← explicitArgs head args
                let explicitJ ← explicit.mapM exprToAst
                return appChain (varJson name.toString) explicitJ
          else
            -- Unknown const head → curried App chain over explicit args.
            let explicit ← explicitArgs head args
            let explicitJ ← explicit.mapM exprToAst
            return appChain (varJson name.toString) explicitJ
      | _ => do
          -- Non-const head (fvar, lambda, projection, …): recurse into
          -- the head and curry over all args (no FunInfo available).
          let headJ ← exprToAst head
          let argJ ← args.mapM exprToAst
          return appChain headJ argJ

/-- Diagnostic: what kind of node did we hit? Useful for coverage reports. -/
def exprHeadKind (e : Expr) : String :=
  match e with
  | .bvar _ => "bvar"
  | .fvar _ => "fvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const n _ => s!"const({n})"
  | .app _ _ =>
      match e.getAppFn with
      | .const n _ => s!"app-of({n})"
      | _ => "app-of(other)"
  | .lam _ _ _ _ => "lam"
  | .forallE _ _ _ _ => "forallE"
  | .letE _ _ _ _ _ => "letE"
  | .lit _ => "lit"
  | .mdata _ _ => "mdata"
  | .proj _ _ _ => "proj"

end PhysLeanExtract
