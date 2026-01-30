import PhysicsGenerator.Derived.EnergyMomentum

/-!
# Einstein's Mass-Energy Equivalence: E = mc² (Derived)

The complete derivation chain from definitions to E = mc²:

  Definition: OnMassShell ≡ E² − |p⃗|²c² = (mc²)²
    ↓ (algebraic rearrangement)
  Theorem: energy_momentum_relation: E² = |p⃗|²c² + (mc²)²
    ↓ (substitute |p⃗|² = 0 for rest frame)
  Theorem: rest_energy_squared: E² = (mc²)²
    ↓ (positive square root, using E ≥ 0, m ≥ 0, c > 0)
  Theorem: rest_energy: E = mc²

No axioms beyond physical constants (c > 0) and the mass-shell
definition are used. All steps are pure algebra over ℝ (Mathlib).
-/

namespace PhysicsGenerator.Derived

open PhysicsGenerator
open PhysicsGenerator.SpecialRelativity

/-- At rest (|p⃗|² = 0), the energy-momentum relation reduces to E² = (mc²)² -/
theorem rest_energy_squared (p : FourMomentum) (m : ℝ)
    (h_shell : OnMassShell p m)
    (h_rest : AtRest p) :
    p.energy ^ 2 = (m * c ^ 2) ^ 2 := by
  have h_em := energy_momentum_relation p m h_shell
  unfold AtRest at h_rest
  rw [h_rest] at h_em
  simp at h_em
  linarith

/-- Einstein's mass-energy equivalence: E = mc²

    For a particle at rest with non-negative energy and non-negative mass.
    Proof: E² = (mc²)² with E ≥ 0 and mc² ≥ 0, so E = mc²
    (take positive square root of both sides). -/
theorem rest_energy (p : FourMomentum) (m : ℝ)
    (hE : 0 ≤ p.energy) (hm : 0 ≤ m)
    (h_shell : OnMassShell p m)
    (h_rest : AtRest p) :
    p.energy = m * c ^ 2 := by
  have h_sq := rest_energy_squared p m h_shell h_rest
  have hmc : 0 ≤ m * c ^ 2 := by positivity
  -- E² = (mc²)² with both sides non-negative ⟹ E = mc²
  -- Apply √ to both sides: √(E²) = √((mc²)²), then simplify
  have h_sqrt := congr_arg Real.sqrt h_sq
  rwa [Real.sqrt_sq hE, Real.sqrt_sq hmc] at h_sqrt

/-- Scalar form: E = mc² from scalar hypotheses.
    This is the form the Rust derivation engine emits. -/
theorem rest_energy_scalar (E m : ℝ)
    (hE : 0 ≤ E) (hm : 0 ≤ m)
    (h_em : E ^ 2 = (m * c ^ 2) ^ 2) :
    E = m * c ^ 2 := by
  have hmc : 0 ≤ m * c ^ 2 := by positivity
  have h_sqrt := congr_arg Real.sqrt h_em
  rwa [Real.sqrt_sq hE, Real.sqrt_sq hmc] at h_sqrt

end PhysicsGenerator.Derived
