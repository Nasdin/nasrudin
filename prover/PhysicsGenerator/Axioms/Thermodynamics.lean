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
axiom internal_energy : ThermoSystem → ℝ

/-- Entropy of a system -/
axiom entropy_sys : IsolatedSystem → Time → ℝ

/-- Temperature of a system -/
axiom temperature : ThermoSystem → ℝ

/-- Heat absorbed during a process -/
axiom heat_absorbed : ThermoSystem → ThermoProcess → ℝ

/-- Work done during a process -/
axiom work_done : ThermoSystem → ThermoProcess → ℝ

/-- Change in internal energy during a process -/
axiom delta_internal : ThermoSystem → ThermoProcess → ℝ

/-- Thermal equilibrium relation -/
axiom in_thermal_eq : ThermoSystem → ThermoSystem → Prop

/-- Zeroth Law: Thermal equilibrium is transitive -/
axiom zeroth_law (A B C : ThermoSystem) :
  in_thermal_eq A B → in_thermal_eq B C → in_thermal_eq A C

/-- First Law: delta_U = Q - W -/
axiom first_law (sys : ThermoSystem) (proc : ThermoProcess) :
  delta_internal sys proc = heat_absorbed sys proc - work_done sys proc

/-- Second Law (Entropy): Entropy of an isolated system never decreases -/
axiom second_law (sys : IsolatedSystem) (t1 t2 : Time) :
  t1 ≤ t2 → entropy_sys sys t1 ≤ entropy_sys sys t2

/-- Second Law (Clausius): No cyclic process has as its sole effect
    the transfer of heat from a colder to a hotter body -/
axiom second_law_clausius :
  ¬∃ (proc : CyclicProcess), sole_effect_is_cold_to_hot proc

/-- Third Law: Entropy approaches zero as temperature approaches zero -/
axiom third_law (sys : ThermoSystem) :
  Filter.Tendsto (fun T => temperature sys) (nhds 0) (nhds 0)

/-- Ideal Gas Law: PV = nRT -/
axiom ideal_gas_law (gas : IdealGas) :
  IdealGas.pressure gas * IdealGas.volume gas =
    IdealGas.moles gas * R_gas * IdealGas.temperature gas

/-- Boltzmann Entropy: S = k_B · ln(Ω) -/
axiom boltzmann_entropy (sys : StatisticalSystem) :
  stat_entropy sys = k_B * Real.log (microstates sys)

end PhysicsGenerator.Thermodynamics
