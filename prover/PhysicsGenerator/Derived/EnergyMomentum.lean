import PhysicsGenerator.Generated.SpecialRelativity

/-!
# Energy-Momentum Relation (Derived)

The relativistic energy-momentum relation:
  E² = |p⃗|²c² + (mc²)²

This is NOT an axiom — it follows by algebraic rearrangement from
the mass-shell condition (a definition of what it means for a
4-momentum to belong to a particle of mass m).

Derivation chain:
  Definition: OnMassShell ≡ E² − |p⃗|²c² = (mc²)²
    ↓ (linarith — algebraic rearrangement)
  Theorem: energy_momentum_relation
-/

namespace PhysicsGenerator.Derived

open PhysicsGenerator
open PhysicsGenerator.SpecialRelativity

/-- Energy-momentum relation: E² = |p⃗|²c² + (mc²)²

    Follows directly from the mass-shell condition by rearrangement:
      E² − |p⃗|²c² = (mc²)²
    ⟹ E² = |p⃗|²c² + (mc²)² -/
theorem energy_momentum_relation (p : FourMomentum) (m : ℝ)
    (h_shell : OnMassShell p m) :
    p.energy ^ 2 = p.three_momentum_sq * c ^ 2 + (m * c ^ 2) ^ 2 := by
  unfold OnMassShell FourMomentum.invariant_mass_energy at h_shell
  linarith

/-- Scalar form of the energy-momentum relation.
    Convenience theorem taking scalar quantities directly. -/
theorem energy_momentum_scalar (E m p_mag : ℝ)
    (h : E ^ 2 - p_mag ^ 2 * c ^ 2 = (m * c ^ 2) ^ 2) :
    E ^ 2 = p_mag ^ 2 * c ^ 2 + (m * c ^ 2) ^ 2 := by
  linarith

end PhysicsGenerator.Derived
