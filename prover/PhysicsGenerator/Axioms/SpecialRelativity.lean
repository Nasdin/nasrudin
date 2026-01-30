import PhysicsGenerator.Basic

/-!
# Special Relativity Axioms

The two postulates of special relativity.
E = mc^2 should be DERIVED, not axiomatized.
-/

namespace PhysicsGenerator.SpecialRelativity

open PhysicsGenerator

/-- An inertial reference frame -/
axiom InertialFrame : Type

/-- A physics law -/
axiom PhysicsLaw : Type

/-- Whether a law holds in a frame -/
axiom holds : PhysicsLaw -> InertialFrame -> Prop

/-- An observer in a frame -/
axiom Observer : InertialFrame -> Type

/-- Measured speed of light by an observer -/
axiom measured_speed_of_light : ∀ (f : InertialFrame), Observer f -> R'

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
axiom spacetime_interval : InertialFrame -> SpacetimeEvent -> SpacetimeEvent -> R'

/-- The spacetime interval is invariant across frames
    (derivable from postulates, included as checkpoint) -/
axiom interval_invariant (e1 e2 : SpacetimeEvent) (f1 f2 : InertialFrame) :
  spacetime_interval f1 e1 e2 = spacetime_interval f2 e1 e2

end PhysicsGenerator.SpecialRelativity
