import Mathlib
import PhysicsGenerator.Basic
import PhysicsGenerator.Generated.SpecialRelativity

/-!
# Photon energy-momentum relation: E_photon = c · p_photon

Phase 7 demo: a *second* modern-physics theorem derived from a
non-SR domain (electromagnetism / quantum optics) using the same
pattern as `RestEnergyUpstream.lean`.

## Upstream EM/quantum axioms (encoded as theorem hypotheses)

  (h_eph    : Eph = hbar · omega)        -- Planck-Einstein
  (h_pph    : pph = hbar · k)            -- de Broglie
  (h_disp   : omega = c · k)             -- massless dispersion
  (hc       : 0 < c)                     -- speed of light positivity
  (hhbar    : 0 < hbar)                  -- reduced Planck positivity

## Derivation chain

  Step 1: substitute `omega = c · k` into `h_eph`
          ⇒ Eph = hbar · (c · k)
  Step 2: rearrange (associativity / commutativity of ·)
          ⇒ Eph = c · (hbar · k)
  Step 3: substitute `pph = hbar · k`
          ⇒ Eph = c · pph

The headline result `E_photon = c · p_photon` is derived; no
"E = c·p" axiom needed.
-/

namespace PhysicsGenerator.Derived

open PhysicsGenerator
open PhysicsGenerator.SpecialRelativity

/-- Photon energy-momentum relation, derived from upstream postulates. -/
theorem photon_energy_momentum
    (Eph pph omega k hbar : ℝ)
    (h_eph  : Eph = hbar * omega)
    (h_pph  : pph = hbar * k)
    (h_disp : omega = c * k)
    (_hc    : 0 < c)
    (_hhbar : 0 < hbar) :
    Eph = c * pph := by
  -- Substitute h_disp into h_eph and h_pph into the goal.
  rw [h_eph, h_disp, h_pph]
  ring

end PhysicsGenerator.Derived
