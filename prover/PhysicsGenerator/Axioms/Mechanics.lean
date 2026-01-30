import PhysicsGenerator.Basic

/-!
# Classical Mechanics Axioms
-/

namespace PhysicsGenerator.Mechanics

open PhysicsGenerator

/-- Newton's Second Law: F = ma
    The net force on a body equals its mass times its acceleration -/
axiom newton_second_law (body : Body) (t : Time) :
  net_force body t = Vec3.mk
    (Body.mass body * (acceleration body t).x)
    (Body.mass body * (acceleration body t).y)
    (Body.mass body * (acceleration body t).z)

/-- Newton's Third Law: Action equals reaction -/
axiom newton_third_law (a b : Body) (t : Time) :
  force_on a b t = Vec3.mk
    (-(force_on b a t).x)
    (-(force_on b a t).y)
    (-(force_on b a t).z)

/-- Conservation of Energy: Total energy of a closed system is constant -/
axiom energy_conservation (sys : ClosedSystem) (t1 t2 : Time) :
  total_energy sys t1 = total_energy sys t2

/-- Conservation of Momentum: Total momentum of a closed system is constant -/
axiom momentum_conservation (sys : ClosedSystem) (t1 t2 : Time) :
  total_momentum sys t1 = total_momentum sys t2

end PhysicsGenerator.Mechanics
