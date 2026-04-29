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

-- Pinned to a tag for build stability. To pick up new PhysLean (and
-- transitively new Mathlib) theorems via `just refresh-corpus`, bump
-- this version manually:
--   - Browse https://github.com/HEPLean/PhysLean/releases for the latest tag.
--   - Edit this line, run `lake update PhysLean && lake build PhysLean`.
--   - The walker's universal translator handles arbitrary new theorem
--     shapes, so no Lean-side code change should be needed.
-- Alternative: track a moving branch with `@ "main"`, accepting that
-- upstream API churn may break the build until our walker catches up.
require PhysLean from git
  "https://github.com/HEPLean/PhysLean.git" @ "v4.26.0"
