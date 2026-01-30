import PhysicsGenerator.Basic

/-!
# General Relativity Axioms
-/

namespace PhysicsGenerator.GeneralRelativity

open PhysicsGenerator

/-- Einstein's Equivalence Principle:
    Gravitational and inertial mass are identical -/
axiom equivalence_principle (body : MassiveBody) :
  gravitational_mass body = inertial_mass body

/-- Einstein Field Equations: G_μν + Λg_μν = (8πG/c⁴) T_μν -/
axiom einstein_field_equations
  (M : Manifold) (g : LorentzMetric M)
  (T : StressEnergyTensor M) (Λ : ℝ) :
  add_stress M (einstein_tensor M g) (scale_stress M Λ (metric_as_stress M g)) =
    scale_stress M (8 * Real.pi * G / c ^ 4) T

/-- Geodesic Motion: Free particles follow geodesics of the metric -/
axiom geodesic_motion (M : Manifold) (g : LorentzMetric M)
  (γ : Curve M) :
  is_free_particle M γ → is_geodesic M g γ

/-- Bianchi Identity: Covariant divergence of the Einstein tensor vanishes -/
axiom bianchi_identity (M : Manifold) (g : LorentzMetric M) :
  covariant_divergence M (einstein_tensor M g) = zero_stress M

end PhysicsGenerator.GeneralRelativity
