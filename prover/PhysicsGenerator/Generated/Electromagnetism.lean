import Mathlib
import PhysicsGenerator.Basic

/-!
# Electromagnetism (Generated from PhysLean)

Auto-generated from PhysLean catalog (version: master).
These axioms correspond to proven theorems in PhysLean.
Re-axiomatized here for Lean 4.27 compatibility.

DO NOT EDIT — regenerate with `just generate-axioms`.
-/

namespace PhysicsGenerator.Electromagnetism

open PhysicsGenerator

-- ══════════════════════════════════════════════════════════════
-- Types (from PhysLean)
-- ══════════════════════════════════════════════════════════════

-- Source: PhysLean (PhysLean.Electromagnetism.FieldStrengthTensor)
/-- FieldStrengthTensor -/
structure FieldStrengthTensor where
  components : Matrix (Fin 4) (Fin 4) ℝ

-- Source: PhysLean (PhysLean.Electromagnetism.FourPotential)
/-- FourPotential -/
structure FourPotential where
  φ : ℝ
  A : Fin 3 → ℝ

-- ══════════════════════════════════════════════════════════════
-- Helper Types (for axiom signatures)
-- ══════════════════════════════════════════════════════════════

/-- Vector field in 3D space -/
axiom VectorField : Type

/-- Scalar field in 3D space -/
axiom ScalarField : Type

axiom div_field : VectorField → ScalarField
axiom curl_field : VectorField → VectorField
axiom time_deriv : VectorField → Time → VectorField
axiom scale_field : ℝ → VectorField → VectorField
axiom add_field : VectorField → VectorField → VectorField
axiom neg_field : VectorField → VectorField
axiom div_scalar : ScalarField → ℝ → ScalarField
axiom zero_scalar : ScalarField
axiom E_field : VectorField
axiom B_field : VectorField
axiom J_field : VectorField
axiom rho_field : ScalarField

-- ══════════════════════════════════════════════════════════════
-- Theorems (from PhysLean — re-axiomatized)
-- ══════════════════════════════════════════════════════════════

-- Source: PhysLean (PhysLean.Electromagnetism.FieldTensor.maxwell_field_tensor)
/-- Maxwell's equations in tensor form -/
axiom maxwell_field_tensor :
  ∀ (F : FieldStrengthTensor), maxwell_from_tensor F ↔ maxwell_equations F

-- Source: PhysLean (PhysLean.Electromagnetism.Potential.electromagnetic_potential)
/-- The field tensor as exterior derivative of the 4-potential -/
axiom electromagnetic_potential :
  ∀ (A : FourPotential), F_from_potential A = exterior_derivative A

-- Source: PhysLean (PhysLean.Electromagnetism.PlaneWave.plane_wave_solution)
/-- Plane wave dispersion relation from Maxwell's equations -/
axiom plane_wave_solution :
  ∀ (k : WaveVector) (ω : ℝ), is_maxwell_solution (plane_wave k ω) → ω = c * |k|

-- Source: PhysLean (PhysLean.Electromagnetism.Gauge.gauge_invariance)
/-- Gauge invariance of the electromagnetic field tensor -/
axiom gauge_invariance :
  ∀ (A : FourPotential) (χ : ScalarField), F_from_potential (A + gauge_transform χ) = F_from_potential A

end PhysicsGenerator.Electromagnetism
