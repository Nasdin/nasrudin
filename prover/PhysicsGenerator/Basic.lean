/-!
# Basic Types for Physics Generator

Foundation types used across the physics axiom modules.
These are placeholder types that will be replaced with Mathlib types
once the Mathlib dependency is enabled.
-/

namespace PhysicsGenerator

-- Placeholder for real numbers (will use Mathlib's R later)
axiom PhysReal : Type
notation "R'" => PhysReal

-- Basic real number operations (axiomatized for now)
axiom PhysReal.zero : R'
axiom PhysReal.one : R'
axiom PhysReal.add : R' -> R' -> R'
axiom PhysReal.mul : R' -> R' -> R'
axiom PhysReal.neg : R' -> R'
axiom PhysReal.inv : R' -> R'
axiom PhysReal.lt : R' -> R' -> Prop
axiom PhysReal.le : R' -> R' -> Prop

noncomputable instance : Add R' := ⟨PhysReal.add⟩
noncomputable instance : Mul R' := ⟨PhysReal.mul⟩
noncomputable instance : Neg R' := ⟨PhysReal.neg⟩

-- 3D Vector (placeholder)
structure Vec3 where
  x : R'
  y : R'
  z : R'

-- Physical quantity with a value
structure Quantity where
  value : R'

-- Time parameter
abbrev Time := R'

-- Physical body
axiom Body : Type
axiom Body.mass : Body -> R'

-- Physical system
axiom System : Type

-- Closed system (no external forces)
axiom ClosedSystem : Type

-- Functions on bodies and systems
axiom velocity : Body -> Time -> Vec3
axiom acceleration : Body -> Time -> Vec3
axiom net_force : Body -> Time -> Vec3
axiom force_on : Body -> Body -> Time -> Vec3

-- Energy and momentum
axiom total_energy : ClosedSystem -> Time -> R'
axiom total_momentum : ClosedSystem -> Time -> Vec3
axiom kinetic_energy : Body -> Time -> R'

-- Physical constants
axiom c : R'   -- Speed of light
axiom G : R'   -- Gravitational constant
axiom h : R'   -- Planck constant
axiom hbar : R' -- Reduced Planck constant
axiom k_B : R' -- Boltzmann constant
axiom eps0 : R' -- Vacuum permittivity
axiom mu0 : R'  -- Vacuum permeability

-- Positivity of constants
axiom c_pos : PhysReal.lt PhysReal.zero c
axiom G_pos : PhysReal.lt PhysReal.zero G
axiom h_pos : PhysReal.lt PhysReal.zero h

end PhysicsGenerator
