import Lake
open Lake DSL

package PhysicsGenerator where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib PhysicsGenerator where
  srcDir := "."

-- Mathlib dependency (large, will take time to build first time)
-- Uncomment when ready to use Mathlib:
-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"
