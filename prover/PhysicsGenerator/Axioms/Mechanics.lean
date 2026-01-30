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

/-- Newton's First Law: A body at rest or in uniform motion stays so
    unless acted upon by a net force -/
axiom newton_first_law (body : Body) (t : Time) :
  net_force body t = ⟨0, 0, 0⟩ → velocity body t = velocity body 0

/-- Conservation of Angular Momentum -/
axiom angular_momentum_conservation (sys : ClosedSystem) (t1 t2 : Time) :
  total_angular_momentum sys t1 = total_angular_momentum sys t2

/-- Principle of Least Action: physical paths extremize the action -/
axiom least_action (path : Path) (t1 t2 : Time) :
  is_physical_path path t1 t2 ↔
  ∀ (other : Path), action_integral lagrangian_default path t1 t2 ≤
    action_integral lagrangian_default other t1 t2

/-- Kinetic energy definition: KE = ½mv² -/
axiom kinetic_energy_def (body : Body) (t : Time) :
  kinetic_energy body t = (1/2) * Body.mass body * Vec3.norm_sq (velocity body t)

/-- Gravitational potential energy near Earth surface: PE = mgh -/
axiom gravitational_pe (body : Body) (h : ℝ) :
  potential_energy_gravity body h = Body.mass body * g_accel * h

/-- Newton's Law of Universal Gravitation: F = G·m₁·m₂/r² -/
axiom universal_gravitation (a b : Body) (r : ℝ) (hr : r > 0) :
  gravitational_force a b r = G * Body.mass a * Body.mass b / r ^ 2

end PhysicsGenerator.Mechanics
