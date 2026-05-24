// Map common Lean / PhysLean type and constant names to compact physics
// symbols so prefix-form `canonical_statement` strings become a little
// less alien when we have to show them as raw text (detail panels,
// fallback cells where `latex` is null).
//
// We do NOT try to parse the S-expression — that's a much bigger
// project. We just string-replace whole identifiers using word
// boundaries so "SpeedOfLight" in `(picv : SpeedOfLight ...)` becomes
// "c" without touching unrelated substrings like "SpeedOfLight_axiom".
const SYMBOL_MAP: Record<string, string> = {
  SpeedOfLight: 'c',
  PlanckConstant: 'h',
  ReducedPlanckConstant: 'ℏ',
  Mass: 'm',
  Energy: 'E',
  Momentum: 'p',
  FourMomentum: 'p⁴',
  Frequency: 'ν',
  Wavelength: 'λ',
  Charge: 'q',
  ElectricCharge: 'q',
  GravitationalConstant: 'G',
  BoltzmannConstant: 'k_B',
  ElectricField: 'E⃗',
  MagneticField: 'B⃗',
  ElectromagneticPotential: 'A_μ',
  Permittivity: 'ε',
  VacuumPermittivity: 'ε₀',
  Permeability: 'μ',
  VacuumPermeability: 'μ₀',
  ProperTime: 'τ',
  Temperature: 'T',
  Entropy: 'S',
  AngularMomentum: 'L',
  AngularVelocity: 'ω',
  Velocity: 'v',
  Acceleration: 'a',
  Force: 'F⃗',
};

const PATTERN = new RegExp(`\\b(${Object.keys(SYMBOL_MAP).join('|')})\\b`, 'g');

/**
 * Replace common Lean physics constant / type names with single-letter
 * symbols. Idempotent and safe on arbitrary strings — non-matching
 * input is returned unchanged.
 */
export function leanToSymbols(s: string): string {
  return s.replace(PATTERN, (m) => SYMBOL_MAP[m] ?? m);
}
