import Mathlib
import PhysicsGenerator.Basic

/-!
# SpecialRelativity (Generated from PhysLean)

Auto-generated from PhysLean catalog (version: master).
These axioms correspond to proven theorems in PhysLean.
Re-axiomatized here for Lean 4.27 compatibility.

DO NOT EDIT — regenerate with `just generate-axioms`.
-/

namespace PhysicsGenerator.SpecialRelativity

open PhysicsGenerator

-- ══════════════════════════════════════════════════════════════
-- Types (from PhysLean)
-- ══════════════════════════════════════════════════════════════

-- Source: PhysLean (PhysLean.Relativity.Special.FourMomentum)
/-- FourMomentum -/
structure FourMomentum where
  energy : ℝ
  px : ℝ
  py : ℝ
  pz : ℝ

-- Source: PhysLean (PhysLean.Relativity.Special.LorentzGroup)
/-- LorentzGroup -/
structure LorentzGroup where
  matrix : Matrix (Fin 4) (Fin 4) ℝ

-- ══════════════════════════════════════════════════════════════
-- Helper Definitions (for derivation proofs)
-- ══════════════════════════════════════════════════════════════

/-- Squared magnitude of 3-momentum: |p⃗|² = px² + py² + pz² -/
noncomputable def FourMomentum.three_momentum_sq (p : FourMomentum) : ℝ :=
  p.px ^ 2 + p.py ^ 2 + p.pz ^ 2

/-- Minkowski invariant (energy scale): E² − |p⃗|²c² -/
noncomputable def FourMomentum.invariant_mass_energy (p : FourMomentum) : ℝ :=
  p.energy ^ 2 - p.three_momentum_sq * c ^ 2

/-- Mass-shell condition: E² − |p⃗|²c² = (mc²)² -/
def OnMassShell (p : FourMomentum) (m : ℝ) : Prop :=
  p.invariant_mass_energy = (m * c ^ 2) ^ 2

/-- A particle is at rest when its 3-momentum vanishes -/
def AtRest (p : FourMomentum) : Prop :=
  p.three_momentum_sq = 0

-- ══════════════════════════════════════════════════════════════
-- Theorems (from PhysLean — re-axiomatized)
-- ══════════════════════════════════════════════════════════════

-- Source: PhysLean (PhysLean.Relativity.Special.LorentzGroup.SL2C.lorentz_group_SL2C)
/-- The Lorentz group is homomorphic to SL(2,C) -/
axiom lorentz_group_SL2C :
  IsGroupHom (SL2C.toLorentz)

-- Source: PhysLean (PhysLean.Relativity.Special.FourMomentum.on_mass_shell)
/-- Mass-shell condition for a relativistic particle -/
axiom four_momentum_on_mass_shell :
  ∀ (p : FourMomentum) (m : ℝ), OnMassShell p m → p.energy ^ 2 - p.three_momentum_sq * c ^ 2 = (m * c ^ 2) ^ 2

-- Source: PhysLean (PhysLean.Relativity.Special.FourMomentum.invariant)
/-- The invariant mass-energy is Lorentz invariant -/
axiom four_momentum_invariant :
  ∀ (p : FourMomentum) (Λ : LorentzGroup), (Λ • p).invariant_mass_energy = p.invariant_mass_energy

-- Source: PhysLean (PhysLean.Relativity.Special.PauliMatrices.pauli_algebra)
/-- Pauli matrix algebra relations -/
axiom pauli_matrices_algebra :
  σ_i * σ_j = δ_ij * I + i * ε_ijk * σ_k

-- Source: PhysLean (PhysLean.Relativity.Special.LorentzGroup.boost_composition)
/-- Relativistic velocity addition (boost composition) -/
axiom lorentz_boost_composition :
  ∀ (v₁ v₂ : ℝ) (hv₁ : |v₁| < c) (hv₂ : |v₂| < c), boost_velocity v₁ v₂ = (v₁ + v₂) / (1 + v₁ * v₂ / c ^ 2)

-- Source: PhysLean (PhysLean.Relativity.Special.TimeDilation.time_dilation)
/-- Time dilation formula -/
axiom time_dilation :
  ∀ (Δt₀ v : ℝ) (hv : |v| < c), dilated_time Δt₀ v = Δt₀ / Real.sqrt (1 - v ^ 2 / c ^ 2)

-- Source: PhysLean (PhysLean.Relativity.Special.LengthContraction.length_contraction)
/-- Length contraction formula -/
axiom length_contraction :
  ∀ (L₀ v : ℝ) (hv : |v| < c), contracted_length L₀ v = L₀ * Real.sqrt (1 - v ^ 2 / c ^ 2)

-- Source: PhysLean (PhysLean.Relativity.Special.TwinParadox.twin_paradox)
/-- The twin paradox: the traveling twin ages less -/
axiom twin_paradox :
  ∀ (journey : TwinJourney), proper_time_traveler journey < proper_time_stationary journey

end PhysicsGenerator.SpecialRelativity
