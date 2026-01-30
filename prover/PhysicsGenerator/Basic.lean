import Mathlib

/-!
# Basic Types for Physics Generator

Foundation types used across the physics axiom modules.
Uses Mathlib's ℝ (real numbers) for full algebraic reasoning.

Domain-specific types (FourMomentum, QState, etc.) are in their
respective Generated/ modules, not here.
-/

namespace PhysicsGenerator

-- 3D Vector over reals
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

-- Physical quantity with a value
structure Quantity where
  value : ℝ

-- Time parameter
abbrev Time := ℝ

-- Physical body
axiom Body : Type
axiom Body.mass : Body → ℝ

-- Physical system
axiom System : Type

-- Closed system (no external forces)
axiom ClosedSystem : Type

-- Functions on bodies and systems
axiom velocity : Body → Time → Vec3
axiom acceleration : Body → Time → Vec3
axiom net_force : Body → Time → Vec3
axiom force_on : Body → Body → Time → Vec3

-- Energy and momentum
axiom total_energy : ClosedSystem → Time → ℝ
axiom total_momentum : ClosedSystem → Time → Vec3
axiom kinetic_energy : Body → Time → ℝ

-- Physical constants (opaque — only properties are asserted, not values)
axiom c : ℝ         -- Speed of light
axiom G : ℝ         -- Gravitational constant
axiom h_planck : ℝ  -- Planck constant
axiom hbar : ℝ      -- Reduced Planck constant
axiom k_B : ℝ       -- Boltzmann constant
axiom eps0 : ℝ      -- Vacuum permittivity
axiom mu0 : ℝ       -- Vacuum permeability
axiom g_accel : ℝ   -- Gravitational acceleration near Earth surface
axiom R_gas : ℝ     -- Universal gas constant

-- Positivity of constants
axiom c_pos : 0 < c
axiom G_pos : 0 < G
axiom h_planck_pos : 0 < h_planck
axiom g_accel_pos : 0 < g_accel
axiom k_B_pos : 0 < k_B
axiom R_gas_pos : 0 < R_gas

-- Vec3 operations
axiom Vec3.norm_sq : Vec3 → ℝ
axiom Vec3.cross : Vec3 → Vec3 → Vec3
noncomputable instance : Zero Vec3 := ⟨⟨0, 0, 0⟩⟩

-- Angular momentum
axiom total_angular_momentum : ClosedSystem → Time → Vec3

-- Gravitational helpers
axiom potential_energy_gravity : Body → ℝ → ℝ
axiom gravitational_force : Body → Body → ℝ → ℝ

-- Action / Lagrangian (abstract)
axiom Path : Type
axiom Lagrangian : Type
axiom action_integral : Lagrangian → Path → Time → Time → ℝ
axiom is_physical_path : Path → Time → Time → Prop
axiom lagrangian_default : Lagrangian

-- Electromagnetism helpers
axiom electromagnetic_force : ℝ → Vec3 → Vec3 → Vec3 → Vec3 → Vec3
axiom electrostatic_force : ℝ → ℝ → ℝ → ℝ

-- Quantum mechanics types
axiom QState : Type
axiom HilbertSpace : Type
axiom unit_sphere : HilbertSpace → Set QState
axiom Observable : Type
axiom Observable.operator : Observable → Observable
axiom is_self_adjoint : Observable → Prop
axiom std_dev : Observable → QState → ℝ
axiom expected_value : Observable → QState → ℝ
axiom FermionSystem : Type
axiom Fermion : Type
axiom quantum_numbers : Fermion → ℕ

-- Thermodynamics helpers
axiom IdealGas : Type
axiom IdealGas.pressure : IdealGas → ℝ
axiom IdealGas.volume : IdealGas → ℝ
axiom IdealGas.moles : IdealGas → ℝ
axiom IdealGas.temperature : IdealGas → ℝ
axiom StatisticalSystem : Type
axiom microstates : StatisticalSystem → ℝ
axiom stat_entropy : StatisticalSystem → ℝ
axiom CyclicProcess : Type
axiom sole_effect_is_cold_to_hot : CyclicProcess → Prop

-- General Relativity types
axiom Manifold : Type
axiom LorentzMetric : Manifold → Type
axiom StressEnergyTensor : Manifold → Type
axiom MassiveBody : Type
axiom gravitational_mass : MassiveBody → ℝ
axiom inertial_mass : MassiveBody → ℝ
axiom einstein_tensor (M : Manifold) : LorentzMetric M → StressEnergyTensor M
axiom metric_as_stress (M : Manifold) : LorentzMetric M → StressEnergyTensor M
axiom scale_stress (M : Manifold) : ℝ → StressEnergyTensor M → StressEnergyTensor M
axiom add_stress (M : Manifold) : StressEnergyTensor M → StressEnergyTensor M → StressEnergyTensor M
axiom covariant_divergence (M : Manifold) : StressEnergyTensor M → StressEnergyTensor M
axiom zero_stress (M : Manifold) : StressEnergyTensor M
axiom Curve : Manifold → Type
axiom is_free_particle (M : Manifold) : Curve M → Prop
axiom is_geodesic (M : Manifold) : LorentzMetric M → Curve M → Prop

end PhysicsGenerator
