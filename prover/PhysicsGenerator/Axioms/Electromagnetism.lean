import PhysicsGenerator.Basic

/-!
# Electromagnetism Axioms (Maxwell's Equations)
-/

namespace PhysicsGenerator.Electromagnetism

open PhysicsGenerator

/-- Vector field in 3D space -/
axiom VectorField : Type

/-- Scalar field in 3D space -/
axiom ScalarField : Type

/-- Divergence operator -/
axiom div_field : VectorField -> ScalarField

/-- Curl operator -/
axiom curl_field : VectorField -> VectorField

/-- Time derivative of a vector field -/
axiom time_deriv : VectorField -> Time -> VectorField

/-- Scale a vector field by a scalar -/
axiom scale_field : R' -> VectorField -> VectorField

/-- Add vector fields -/
axiom add_field : VectorField -> VectorField -> VectorField

/-- Negate a vector field -/
axiom neg_field : VectorField -> VectorField

/-- Divide scalar field by constant -/
axiom div_scalar : ScalarField -> R' -> ScalarField

/-- Zero scalar field -/
axiom zero_scalar : ScalarField

/-- Electric field -/
axiom E_field : VectorField

/-- Magnetic field -/
axiom B_field : VectorField

/-- Current density -/
axiom J_field : VectorField

/-- Charge density -/
axiom rho_field : ScalarField

/-- Gauss's Law: div(E) = rho/eps0 -/
axiom gauss_law : div_field E_field = div_scalar rho_field eps0

/-- Gauss's Law for Magnetism: div(B) = 0 (no magnetic monopoles) -/
axiom gauss_law_magnetism :
  div_field B_field = zero_scalar

/-- Faraday's Law: curl(E) = -dB/dt -/
axiom faraday_law (t : Time) :
  curl_field E_field = neg_field (time_deriv B_field t)

/-- Ampere-Maxwell Law: curl(B) = mu0*J + mu0*eps0 * dE/dt -/
axiom ampere_maxwell (t : Time) :
  curl_field B_field = add_field
    (scale_field mu0 J_field)
    (scale_field (mu0 * eps0) (time_deriv E_field t))

end PhysicsGenerator.Electromagnetism
