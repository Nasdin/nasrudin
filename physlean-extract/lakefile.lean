import Lake
open Lake DSL

package PhysLeanExtract where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib PhysLeanExtract where
  srcDir := "."

lean_exe extract where
  root := `PhysLeanExtract.Main

-- Self-contained translator tests. Independent of PhysLean — runs
-- against a handful of inline `theorem` declarations whose ASTs are
-- verifiable by inspection. Useful for iterating on `exprToAst`
-- without paying the multi-hour PhysLean build cost.
lean_exe test_expr_ast where
  root := `PhysLeanExtract.TestRunner

require PhysLean from git
  "https://github.com/HEPLean/PhysLean.git" @ "v4.26.0"
