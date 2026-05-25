// Single source of truth for how Domain enum values are presented in the
// UI. The backend ships `domain: "SpecialRelativity"` style enum strings;
// the user-facing label and the colour treatment live here so the landing
// browser, the theorem page, the live ticker, and any future surface all
// agree.
//
// We deliberately collapse some neighbouring enums (e.g. SpecialRelativity
// and GeneralRelativity both display as "Relativity") because for a
// visiting reader those distinctions don't carry their weight at the
// top-of-page badge level — the sidebar's Tech-details panel still shows
// the raw enum.

export type DomainCategory =
  | 'pure-math'
  | 'classical'
  | 'electromagnetism'
  | 'relativity'
  | 'quantum'
  | 'other';

export interface DomainPresentation {
  label: string;
  category: DomainCategory;
  /** One-line tagline shown under the domain pill on the theorem page. */
  tagline: string;
}

const TABLE: Record<string, DomainPresentation> = {
  PureMath: {
    label: 'Pure mathematics',
    category: 'pure-math',
    tagline: 'Lemmas with no physics interpretation — pure structural math.',
  },
  ClassicalMechanics: {
    label: 'Classical mechanics',
    category: 'classical',
    tagline: 'Newtonian / Lagrangian / Hamiltonian regime.',
  },
  Thermodynamics: {
    label: 'Thermodynamics',
    category: 'classical',
    tagline: 'Macroscopic energy, entropy, and temperature laws.',
  },
  StatisticalMechanics: {
    label: 'Statistical mechanics',
    category: 'classical',
    tagline: 'Microstate counting → macrostate predictions.',
  },
  FluidDynamics: {
    label: 'Fluid dynamics',
    category: 'classical',
    tagline: 'Continuum flow of liquids and gases.',
  },
  Electromagnetism: {
    label: 'Electromagnetism',
    category: 'electromagnetism',
    tagline: 'Maxwell-equation regime — fields, potentials, charges.',
  },
  Optics: {
    label: 'Optics',
    category: 'electromagnetism',
    tagline: 'Wave and ray treatment of light.',
  },
  SpecialRelativity: {
    label: 'Special relativity',
    category: 'relativity',
    tagline: 'Lorentz-invariant flat-spacetime physics.',
  },
  GeneralRelativity: {
    label: 'General relativity',
    category: 'relativity',
    tagline: 'Curved-spacetime / Einstein-equations regime.',
  },
  QuantumMechanics: {
    label: 'Quantum mechanics',
    category: 'quantum',
    tagline: 'Schrödinger / Heisenberg evolution of wavefunctions.',
  },
  QuantumFieldTheory: {
    label: 'Quantum field theory',
    category: 'quantum',
    tagline: 'Fields, operators, and renormalisation group flow.',
  },
};

export function domainPresentation(raw: string | null | undefined): DomainPresentation {
  if (!raw) {
    return {
      label: 'Uncategorised',
      category: 'other',
      tagline: 'No domain tag on this theorem.',
    };
  }
  const hit = TABLE[raw];
  if (hit) return hit;
  return {
    label: raw,
    category: 'other',
    tagline: 'Domain not yet categorised.',
  };
}

/** Used by the landing-page filter chips (one entry per category). */
export const FILTER_CATEGORIES: { label: string; category: DomainCategory | 'all' }[] = [
  { label: 'All', category: 'all' },
  { label: 'Quantum', category: 'quantum' },
  { label: 'Relativity', category: 'relativity' },
  { label: 'Classical mechanics', category: 'classical' },
  { label: 'Electromagnetism', category: 'electromagnetism' },
  { label: 'Pure math', category: 'pure-math' },
];
