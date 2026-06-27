-- Real-arithmetic + carriers
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Defs

-- Transcendentals and order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- Tactics the emitter uses to close goals
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Pre-compiled leaf imports for auto-generated discovery files.

Every `Submission_<id>.lean` and `Discover<n>.lean` produced by the GA
imports this module instead of `import Mathlib`. The full Mathlib import
loads ~400k declarations into elaborator scope, costing 10-20s per
verification even with a warm `.lake/build/` cache. This curated subset
covers everything the GA's chains actually reach: real arithmetic, sqrt,
exp/log/trig, nat/int/complex carriers, and the proof tactics the
emitter uses (`linarith`/`nlinarith`/`polyrith`/`ring`/`norm_num`/
`positivity`).

Compile this once via `lake build PhysicsGenerator.LeafImports` and the
prover's `.lake/build/lib/lean/PhysicsGenerator/LeafImports.olean` is
reused for every subsequent submission. Adding a Mathlib lemma the GA
can't reach yet? Add the corresponding `import Mathlib.X` line above
and rebuild.
-/
