import PhysicsGenerator.Basic

/-!
# Thermodynamics Axioms
-/

namespace PhysicsGenerator.Thermodynamics

open PhysicsGenerator

/-- A thermodynamic system -/
axiom ThermoSystem : Type

/-- An isolated system -/
axiom IsolatedSystem : Type

/-- A thermodynamic process -/
axiom ThermoProcess : Type

/-- Internal energy of a system -/
axiom internal_energy : ThermoSystem -> R'

/-- Entropy of a system -/
axiom entropy_sys : IsolatedSystem -> Time -> R'

/-- Temperature of a system -/
axiom temperature : ThermoSystem -> R'

/-- Heat absorbed during a process -/
axiom heat_absorbed : ThermoSystem -> ThermoProcess -> R'

/-- Work done during a process -/
axiom work_done : ThermoSystem -> ThermoProcess -> R'

/-- Change in internal energy during a process -/
axiom delta_internal : ThermoSystem -> ThermoProcess -> R'

/-- Thermal equilibrium relation -/
axiom in_thermal_eq : ThermoSystem -> ThermoSystem -> Prop

/-- Zeroth Law: Thermal equilibrium is transitive -/
axiom zeroth_law (A B C : ThermoSystem) :
  in_thermal_eq A B -> in_thermal_eq B C -> in_thermal_eq A C

/-- First Law: delta_U = Q - W -/
axiom first_law (sys : ThermoSystem) (proc : ThermoProcess) :
  delta_internal sys proc =
    PhysReal.add (heat_absorbed sys proc) (PhysReal.neg (work_done sys proc))

/-- Second Law: Entropy of an isolated system never decreases -/
axiom second_law (sys : IsolatedSystem) (t1 t2 : Time) :
  PhysReal.le t1 t2 -> PhysReal.le (entropy_sys sys t1) (entropy_sys sys t2)

end PhysicsGenerator.Thermodynamics
