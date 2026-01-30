import PhysicsGenerator.Basic

/-!
# Special Relativity Axioms & Definitions

The two postulates of special relativity, plus the mathematical structure
of Minkowski space (4-momentum, mass-shell condition).

E = mc² is DERIVED in `Derived/RestEnergy.lean`, not axiomatized here.
The energy-momentum relation is a THEOREM from the mass-shell definition.
-/

namespace PhysicsGenerator.SpecialRelativity

open PhysicsGenerator

-- ══════════════════════════════════════════════════════════════
-- SR Postulates
-- ══════════════════════════════════════════════════════════════

/-- An inertial reference frame -/
axiom InertialFrame : Type

/-- A physics law -/
axiom PhysicsLaw : Type

/-- Whether a law holds in a frame -/
axiom holds : PhysicsLaw → InertialFrame → Prop

/-- An observer in a frame -/
axiom Observer : InertialFrame → Type

/-- Measured speed of light by an observer -/
axiom measured_speed_of_light : ∀ (f : InertialFrame), Observer f → ℝ

/-- Postulate 1: The laws of physics are the same in all inertial frames -/
axiom sr_postulate_1 :
  ∀ (law : PhysicsLaw) (f1 f2 : InertialFrame),
  holds law f1 ↔ holds law f2

/-- Postulate 2: The speed of light in vacuum is the same
    for all inertial observers -/
axiom sr_postulate_2 :
  ∀ (f : InertialFrame) (obs : Observer f),
  measured_speed_of_light f obs = c

/-- A spacetime event -/
axiom SpacetimeEvent : Type

/-- Spacetime interval between two events in a frame -/
axiom spacetime_interval : InertialFrame → SpacetimeEvent → SpacetimeEvent → ℝ

/-- The spacetime interval is invariant across frames
    (derivable from postulates, included as checkpoint) -/
axiom interval_invariant (e1 e2 : SpacetimeEvent) (f1 f2 : InertialFrame) :
  spacetime_interval f1 e1 e2 = spacetime_interval f2 e1 e2

-- ══════════════════════════════════════════════════════════════
-- Minkowski Space: 4-Momentum & Mass Shell (Definitions)
-- ══════════════════════════════════════════════════════════════

/-- A relativistic particle's energy-momentum 4-vector.
    Components: (E, px, py, pz) where E is total energy and
    (px,py,pz) is the 3-momentum vector. -/
structure FourMomentum where
  energy : ℝ
  px : ℝ
  py : ℝ
  pz : ℝ

/-- Squared magnitude of 3-momentum: |p⃗|² = px² + py² + pz² -/
noncomputable def FourMomentum.three_momentum_sq (p : FourMomentum) : ℝ :=
  p.px ^ 2 + p.py ^ 2 + p.pz ^ 2

/-- Minkowski invariant (energy scale):
    E² − |p⃗|²c²
    For a massive particle, this equals (mc²)². -/
noncomputable def FourMomentum.invariant_mass_energy (p : FourMomentum) : ℝ :=
  p.energy ^ 2 - p.three_momentum_sq * c ^ 2

/-- Mass-shell condition: a particle of rest mass m satisfies
    E² − |p⃗|²c² = (mc²)²

    This is a DEFINITION — it defines what it means for a
    4-momentum to correspond to a particle of mass m. The
    energy-momentum relation E² = |p⃗|²c² + (mc²)² follows
    by algebraic rearrangement (see Derived/EnergyMomentum.lean). -/
def OnMassShell (p : FourMomentum) (m : ℝ) : Prop :=
  p.invariant_mass_energy = (m * c ^ 2) ^ 2

/-- A particle is at rest when its 3-momentum vanishes -/
def AtRest (p : FourMomentum) : Prop :=
  p.three_momentum_sq = 0

end PhysicsGenerator.SpecialRelativity
