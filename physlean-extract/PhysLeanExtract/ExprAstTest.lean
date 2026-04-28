import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PhysLeanExtract.ExprAst

/-!
# Self-contained tests for `exprToAst`

These tests don't need PhysLean — they just import Mathlib and use a
handful of inline `theorem` declarations whose types we know exactly.
After the extractor runs, the JSON output should contain a populated
`expr_ast` for each of these.

Run via the dedicated `test_expr_ast` exe (see `lakefile.lean`):

    lake exe test_expr_ast

Expected output (ASTs may pretty-print slightly differently):

    a + b = b + a
      → {"BinOp": ["Eq", {"BinOp": ["Add", {"Var":"a"}, {"Var":"b"}]},
                          {"BinOp": ["Add", {"Var":"b"}, {"Var":"a"}]}]}
    (a + b) ^ 2 = a^2 + 2 * a * b + b^2
      → {"BinOp": ["Eq", {"BinOp": ["Pow", ..., {"Lit":[2,1]}]}, ...]}
-/

namespace PhysLeanExtract.Test

open Lean Meta

-- Tiny corpus of theorems with statements the translator should handle.
theorem real_add_comm (a b : ℝ) : a + b = b + a := by ring
theorem real_mul_comm (a b : ℝ) : a * b = b * a := by ring
theorem square_diff (a b : ℝ) : (a - b) * (a + b) = a^2 - b^2 := by ring
theorem rest_energy_shape (E m c : ℝ) (h : E = m * c^2) : E = m * c^2 := h

private def runOne (n : Name) : MetaM Unit := do
  let env ← getEnv
  match env.find? n with
  | none => IO.println s!"  ✗ {n}: not found in env"
  | some ci =>
      match ← exprToAst ci.type with
      | none => IO.println s!"  ✗ {n}: outside supported subset (head = {exprHeadKind ci.type})"
      | some j => IO.println s!"  ✓ {n}\n      {j.compress}"

def runTests : MetaM Unit := do
  IO.println "ExprAst sanity tests"
  IO.println "===================="
  runOne ``real_add_comm
  runOne ``real_mul_comm
  runOne ``square_diff
  runOne ``rest_energy_shape

end PhysLeanExtract.Test
