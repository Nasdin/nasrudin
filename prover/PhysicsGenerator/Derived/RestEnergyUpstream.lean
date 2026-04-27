import Mathlib
import PhysicsGenerator.Basic
import PhysicsGenerator.Generated.SpecialRelativity

/-!
# E = mc² from truly upstream axioms (no mass-shell shortcut)

This file proves Einstein's rest-energy theorem starting from a fundamental
axiom set that does **not** contain the mass-shell condition
`E² − p²c² = (mc²)²` as a primitive. Instead, mass-shell is *derived* as
an intermediate theorem from the four-momentum / Minkowski-invariant
postulates.

## Upstream axioms (encoded as theorem hypotheses)

  (h_mink   : Msq = p0² − psq)         -- definition of Minkowski invariant
  (h_mass   : Msq = m² · c²)           -- postulate: invariant equals m²c²
  (h_four   : c · p0 = E)              -- def: E = c·(time component)
  (h_rest   : psq = 0)                 -- rest-frame existence
  (hE       : 0 ≤ E)
  (hm       : 0 ≤ m)
  (hc       : 0 < c)                   -- speed of light positivity

## Derivation chain

  Step 1: substitute h_rest into h_mink → `Msq = p0²`
  Step 2: combine with h_mass            → `p0² = m² · c²`     (mass-shell-like)
  Step 3: m·c ≥ 0 and p0 ≥ 0 (from c·p0 = E ≥ 0, c > 0)
  Step 4: take positive square root      → `p0 = m · c`
  Step 5: substitute into h_four         → `c · (m · c) = E`
  Step 6: simplify                       → `E = m · c²`

The mass-shell theorem `E² − p²c² = m²·c⁴` is a corollary of step 2 plus
the four_momentum_time_component axiom, multiplied by c² and rewritten.
We prove that as a separate lemma for completeness.
-/

namespace PhysicsGenerator.Derived

open PhysicsGenerator
open PhysicsGenerator.SpecialRelativity

/-- Mass-shell theorem (DERIVED, not axiom): from the upstream postulates,
    `E² − psq · c² = m² · c⁴`. Note `psq` here stands for the squared
    spatial-momentum magnitude `|p⃗|²`. -/
theorem mass_shell_from_upstream
    (E m p0 psq Msq : ℝ)
    (h_mink : Msq = p0 ^ 2 - psq)
    (h_mass : Msq = m ^ 2 * c ^ 2)
    (h_four : c * p0 = E)
    (hc     : 0 < c) :
    E ^ 2 - psq * c ^ 2 = m ^ 2 * c ^ 4 := by
  -- p0² = Msq + psq from h_mink
  have h_p0sq : p0 ^ 2 = Msq + psq := by linarith [h_mink]
  -- (c·p0)² = c²·p0² = c²·(Msq + psq) = c²·Msq + c²·psq
  -- And c·p0 = E, so E² = c²·Msq + c²·psq.
  have h_E_sq : E ^ 2 = c ^ 2 * Msq + c ^ 2 * psq := by
    have hsq := congr_arg (· ^ 2) h_four        -- (c·p0)^2 = E^2
    -- (c·p0)^2 = c^2 · p0^2
    have : (c * p0) ^ 2 = c ^ 2 * p0 ^ 2 := by ring
    nlinarith [hsq, this, h_p0sq]
  -- Substitute h_mass: c² · Msq = c² · m² · c² = m² · c⁴
  have h_mass_c2 : c ^ 2 * Msq = m ^ 2 * c ^ 4 := by
    rw [h_mass]; ring
  -- Therefore E² = m²c⁴ + c²·psq, i.e. E² − c²·psq = m²·c⁴.
  linarith [h_E_sq, h_mass_c2]

/-- E = mc² (REST-ENERGY THEOREM) derived from truly upstream axioms.
    No `mass_shell_condition` axiom needed. -/
theorem rest_energy_from_upstream
    (E m p0 psq Msq : ℝ)
    (h_mink : Msq = p0 ^ 2 - psq)
    (h_mass : Msq = m ^ 2 * c ^ 2)
    (h_four : c * p0 = E)
    (h_rest : psq = 0)
    (hE     : 0 ≤ E)
    (hm     : 0 ≤ m)
    (hc     : 0 < c) :
    E = m * c ^ 2 := by
  -- Step 1+2: combine to get p0² = m² · c²
  have h_p0sq : p0 ^ 2 = m ^ 2 * c ^ 2 := by
    -- Msq = p0² − psq, psq = 0 ⇒ Msq = p0²
    have : Msq = p0 ^ 2 := by rw [h_rest] at h_mink; linarith [h_mink]
    -- and Msq = m² · c²
    linarith [this, h_mass]
  -- Step 3: p0 ≥ 0. From c·p0 = E ≥ 0 and c > 0.
  have hp0 : 0 ≤ p0 := by
    have h_cp0 : c * p0 = E := h_four
    nlinarith [h_cp0, hc, hE]
  -- Step 3b: m · c ≥ 0
  have hmc : 0 ≤ m * c := by positivity
  -- Step 4: p0 = m · c (positive square root of p0² = (m·c)²)
  have h_p0 : p0 = m * c := by
    have hsq : p0 ^ 2 = (m * c) ^ 2 := by
      rw [h_p0sq]; ring
    have h_sqrt := congr_arg Real.sqrt hsq
    rwa [Real.sqrt_sq hp0, Real.sqrt_sq hmc] at h_sqrt
  -- Step 5+6: substitute into h_four and simplify.
  -- c · (m · c) = E ⇒ m · c² = E ⇒ E = m · c²
  rw [h_p0] at h_four
  linarith [h_four]

end PhysicsGenerator.Derived
