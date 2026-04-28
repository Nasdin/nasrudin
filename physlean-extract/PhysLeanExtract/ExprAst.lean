import Lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lean → nasrudin_core::Expr AST translator

Walks a Lean `Expr` tree and emits a JSON object whose shape matches the
`nasrudin_core::Expr` enum (engine/crates/core/src/expr.rs). Only a small
subset of Lean is supported — enough to capture real-arithmetic equations
of the form physics axioms typically take (`E = m·c²`, `(√a)² = a`, etc.).

Anything outside the subset returns `none` and gets logged as a skip
reason. The Rust side (AxiomStore) only loads entries with a populated
`expr_ast` field.

Wire shape (matches `Expr`'s `#[derive(Serialize, Deserialize)]`):

  Var(String)                     →  {"Var": "E"}
  Const(PhysConst)                →  {"Const": "SpeedOfLight"}
  Lit(num, den)                   →  {"Lit": [num, den]}
  BinOp(op, lhs, rhs)             →  {"BinOp": ["Add"|"Sub"|"Mul"|"Div"|"Pow"|"Eq", <lhs>, <rhs>]}
  UnaryOp(op, arg)                →  {"UnaryOp": ["Neg"|"Sqrt", <arg>]}

The 7-variant Expr enum is what the GA's Chain::execute walks; matching
that exact shape means the catalog's `expr_ast` deserializes directly
into an Axiom statement with no glue code.
-/

namespace PhysLeanExtract

open Lean Meta

/-- A handful of named physics constants we recognise on the LHS/RHS of
    Lean equations. Names match `nasrudin_core::PhysConst`. -/
private def physConstName : Name → Option String
  -- Speed of light: PhysLean exposes this as `PhysLean.SpeedOfLight` or
  -- a few aliases; ground-instance forms also appear as the raw symbol
  -- `c` after carrier specialisation.
  | `PhysLean.SpeedOfLight        => some "SpeedOfLight"
  | `PhysLean.PhysicalConstants.c => some "SpeedOfLight"
  | `PhysLean.PhysicalConstants.G => some "GravitationalConstant"
  | `PhysLean.PhysicalConstants.hbar => some "Hbar"
  | `PhysLean.PhysicalConstants.k_B => some "BoltzmannConstant"
  | _ => none

/-- Pull out a Nat literal from a `Lean.Expr` if it has one. Handles the
    common encodings: `OfNat.ofNat n`, `Nat.succ ... Nat.zero`, raw
    `Expr.lit (Literal.natVal n)`. -/
private partial def asNatLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) _) n) _ => asNatLit? n
  | _ => none

/-- Recognise the subset of Lean `Expr` heads we translate as binary
    operators. The tuple (head-name, arg-count-to-pop) tells the walker
    which arguments are operands vs. type/instance carriers. For
    `HAdd.hAdd α β γ inst a b` we always want the *last two* arguments,
    regardless of how many universe / type / instance args precede them. -/
private def binOpFor : Name → Option String
  | ``HAdd.hAdd => some "Add"
  | ``HSub.hSub => some "Sub"
  | ``HMul.hMul => some "Mul"
  | ``HDiv.hDiv => some "Div"
  | ``HPow.hPow => some "Pow"
  | ``Eq        => some "Eq"
  | _           => none

/-- Recognise unary operators. -/
private def unOpFor : Name → Option String
  | ``Neg.neg   => some "Neg"
  | ``Real.sqrt => some "Sqrt"
  | _           => none

/-- Translate a Lean `Expr` into a `Json` tree matching nasrudin_core::Expr,
    or `none` if the term is outside the supported subset.

    The translator runs after `Meta.whnf`-style elaboration so type-class
    instances are usually filled in. Callers should pass a fully-elaborated
    type expression (`val.type` from a `ConstantInfo`).

    Free variables of `Real`-type become `Var(name)`. Bound variables
    inside `forallE` binders are visited inside the binder so their
    `fvarId` is in scope. -/
partial def exprToAst (e : Expr) : MetaM (Option Json) := do
  match e with
  -- Literals -------------------------------------------------------------
  | .lit (.natVal n) =>
      return some <| Json.mkObj [("Lit", Json.arr #[Json.num (JsonNumber.fromInt (Int.ofNat n)), Json.num (JsonNumber.fromInt 1)])]

  -- Named constants ------------------------------------------------------
  | .const name _ =>
      match physConstName name with
      | some pc => return some <| Json.mkObj [("Const", Json.str pc)]
      | none =>
          -- Treat any other zero-arg `Real` constant as a free `Var`
          -- (e.g. `Real.pi`, custom carrier-specialised names).
          let str := name.toString
          return some <| Json.mkObj [("Var", Json.str str)]

  -- Free variables (after entering binders) ------------------------------
  | .fvar fvarId =>
      let decl ← fvarId.getDecl
      return some <| Json.mkObj [("Var", Json.str decl.userName.toString)]

  -- Universal binders (`∀ x : ℝ, ...`) →  recurse into body with the
  -- binder introduced as an FVar so its name appears in `Var(...)`.
  | .forallE _ _ _ _ =>
      forallTelescope e fun _xs body => exprToAst body

  -- Application chains ---------------------------------------------------
  | .app _ _ =>
      let head := e.getAppFn
      let args := e.getAppArgs
      match head with
      | .const name _ =>
          -- BinOp: take the last two args, ignore type / instance carriers.
          if let some op := binOpFor name then
            if args.size >= 2 then
              let lhs ← exprToAst args[args.size - 2]!
              let rhs ← exprToAst args[args.size - 1]!
              match lhs, rhs with
              | some l, some r =>
                  return some <| Json.mkObj
                    [("BinOp", Json.arr #[Json.str op, l, r])]
              | _, _ => return none
            else return none
          -- UnaryOp: take last arg.
          else if let some op := unOpFor name then
            if args.size >= 1 then
              let inner ← exprToAst args[args.size - 1]!
              match inner with
              | some i =>
                  return some <| Json.mkObj
                    [("UnaryOp", Json.arr #[Json.str op, i])]
              | none => return none
            else return none
          -- OfNat numeric literal: `OfNat.ofNat <type> (Nat.lit n)`.
          else if name == ``OfNat.ofNat then
            match asNatLit? e with
            | some n =>
                return some <| Json.mkObj
                  [("Lit", Json.arr #[Json.num (JsonNumber.fromInt (Int.ofNat n)), Json.num (JsonNumber.fromInt 1)])]
            | none => return none
          else return none
      | _ => return none

  -- Anything else (lambdas, `proj`, `mdata`, `mvar`, …) → reject.
  | _ => return none

/-- Diagnostic: what kind of node did we hit? Useful for the
    `skipped: 14127 — references CategoryTheory` style coverage report. -/
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
