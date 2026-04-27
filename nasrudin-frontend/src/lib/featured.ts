export interface Rediscovery {
  formula: string;
  name: string;
  domain: string;
  found: boolean;
  cycle: string;
  elapsed: string;
  proofLines?: number;
  note: string;
}

export const FEATURED_REDISCOVERIES: Rediscovery[] = [
  {
    formula: 'E = mc^2',
    name: 'Mass-energy equivalence',
    domain: 'Special relativity',
    found: true,
    cycle: 'GA-cycle 4,218,107',
    elapsed: '31 d · 14 h',
    proofLines: 47,
    note: 'Emerged from Lorentz invariance + conservation of momentum.',
  },
  {
    formula: 'F = ma',
    name: "Newton's second law",
    domain: 'Classical mechanics',
    found: true,
    cycle: 'GA-cycle 812,044',
    elapsed: '6 d · 3 h',
    proofLines: 12,
    note: "First major rediscovery. The system was 'surprised' by simplicity.",
  },
  {
    formula: 'S = k_B \\ln \\Omega',
    name: 'Boltzmann entropy',
    domain: 'Statistical mechanics',
    found: true,
    cycle: 'GA-cycle 9,847,331',
    elapsed: '78 d · 9 h',
    proofLines: 184,
    note: 'Required first introducing combinatorial counting axioms.',
  },
  {
    formula: 'i\\hbar\\dot\\psi = \\hat H \\psi',
    name: 'Schrödinger equation',
    domain: 'Quantum mechanics',
    found: false,
    cycle: 'search active',
    elapsed: 'candidate #41,082',
    note: 'Closest match to date — missing complex-Hilbert structure axiom.',
  },
  {
    formula: 'R_{\\mu\\nu} - \\tfrac12 g_{\\mu\\nu} R = 8\\pi T_{\\mu\\nu}',
    name: 'Einstein field equations',
    domain: 'General relativity',
    found: false,
    cycle: 'search not started',
    elapsed: 'tensor calculus pending',
    note: 'Awaiting Mathlib differential-geometry expansion.',
  },
  {
    formula: '\\nabla\\cdot E = \\rho/\\varepsilon_0',
    name: "Gauss's law",
    domain: 'Electromagnetism',
    found: true,
    cycle: 'GA-cycle 2,109,553',
    elapsed: '16 d · 22 h',
    proofLines: 38,
    note: 'Co-derived alongside three other Maxwell equations in same week.',
  },
];
