import Lean
import PhysLeanExtract.ExprAstTest

/-! Test-runner entry point. Loads the inline test module and exercises
    `exprToAst` against its theorems. -/

open Lean

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules
    #[ { module := `PhysLeanExtract.ExprAstTest } ] {} 0
  let coreCtx : Lean.Core.Context :=
    { fileName := "<test_expr_ast>", fileMap := .ofString "" }
  let coreState : Lean.Core.State := { env }
  let _ ← (PhysLeanExtract.Test.runTests : Meta.MetaM Unit).run'.toIO coreCtx coreState
