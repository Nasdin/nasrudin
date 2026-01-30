export interface TheoremVariable {
  name: string
  symbol: string
  unit: string
  defaultValue?: number
}

export interface TheoremCompute {
  target: string
  targetSymbol: string
  targetUnit: string
  compute: (vars: Record<string, number>) => number
  resultLatex: (result: number) => string
}

export interface Theorem {
  id: string
  latex: string
  domain: string
  depth: number
  fitness: number
  generation: number
  timestamp?: string
  operator?: string
  name?: string
  variables?: TheoremVariable[]
  computation?: TheoremCompute
}

export interface Axiom {
  id: string
  latex: string
  name: string
  domain: string
}

export interface Stats {
  total_theorems: number
  rate: number
  generation: number
  verified_pct: number
}

export const mockStats: Stats = {
  total_theorems: 347291,
  rate: 142,
  generation: 5021,
  verified_pct: 94.2,
}

export const mockTheorems: Theorem[] = [
  {
    id: 'thm-001',
    latex: 'E = mc^2',
    domain: 'Special Relativity',
    depth: 3,
    fitness: 0.98,
    generation: 4012,
    timestamp: '2025-01-30T14:23:01Z',
    operator: 'Crossover',
  },
  {
    id: 'thm-002',
    latex: 'F = ma',
    domain: 'Classical Mechanics',
    depth: 1,
    fitness: 0.95,
    generation: 102,
    timestamp: '2025-01-30T14:22:48Z',
    operator: 'Mutation',
  },
  {
    id: 'thm-003',
    latex: '\\nabla \\times B = \\mu_0 J + \\mu_0 \\epsilon_0 \\frac{\\partial E}{\\partial t}',
    domain: 'Electromagnetism',
    depth: 5,
    fitness: 0.91,
    generation: 4850,
    timestamp: '2025-01-30T14:22:30Z',
    operator: 'Crossover',
  },
  {
    id: 'thm-004',
    latex: 'i\\hbar \\frac{\\partial}{\\partial t}\\Psi = \\hat{H}\\Psi',
    domain: 'Quantum Mechanics',
    depth: 4,
    fitness: 0.93,
    generation: 3200,
    timestamp: '2025-01-30T14:22:15Z',
    operator: 'Selection',
  },
  {
    id: 'thm-005',
    latex: '\\frac{1}{2}mv^2',
    domain: 'Classical Mechanics',
    depth: 2,
    fitness: 0.89,
    generation: 520,
    timestamp: '2025-01-30T14:21:58Z',
    operator: 'Mutation',
  },
  {
    id: 'thm-006',
    latex: 'E^2 = (pc)^2 + (mc^2)^2',
    domain: 'Special Relativity',
    depth: 4,
    fitness: 0.96,
    generation: 4100,
    timestamp: '2025-01-30T14:21:40Z',
    operator: 'Crossover',
  },
  {
    id: 'thm-007',
    latex: '\\nabla \\cdot E = \\frac{\\rho}{\\epsilon_0}',
    domain: 'Electromagnetism',
    depth: 2,
    fitness: 0.94,
    generation: 1800,
    timestamp: '2025-01-30T14:21:22Z',
    operator: 'Selection',
  },
  {
    id: 'thm-008',
    latex: 'PV = nRT',
    domain: 'Thermodynamics',
    depth: 1,
    fitness: 0.92,
    generation: 340,
    timestamp: '2025-01-30T14:21:05Z',
    operator: 'Mutation',
  },
  {
    id: 'thm-009',
    latex: 'ds^2 = c^2 dt^2 - dx^2 - dy^2 - dz^2',
    domain: 'Special Relativity',
    depth: 3,
    fitness: 0.97,
    generation: 3980,
    timestamp: '2025-01-30T14:20:48Z',
    operator: 'Crossover',
  },
  {
    id: 'thm-010',
    latex: '\\Delta S \\geq 0',
    domain: 'Thermodynamics',
    depth: 2,
    fitness: 0.90,
    generation: 780,
    timestamp: '2025-01-30T14:20:30Z',
    operator: 'Selection',
  },
]

export const mockAxioms: Record<string, Axiom[]> = {
  'Classical Mechanics': [
    {
      id: 'ax-cm-1',
      latex: '\\vec{F} = m\\vec{a}',
      name: "Newton's Second Law",
      domain: 'Classical Mechanics',
    },
    {
      id: 'ax-cm-2',
      latex: '\\vec{F}_{12} = -\\vec{F}_{21}',
      name: "Newton's Third Law",
      domain: 'Classical Mechanics',
    },
    {
      id: 'ax-cm-3',
      latex: '\\frac{d\\vec{p}}{dt} = 0 \\quad \\text{(isolated system)}',
      name: 'Conservation of Momentum',
      domain: 'Classical Mechanics',
    },
    {
      id: 'ax-cm-4',
      latex: '\\frac{dE}{dt} = 0 \\quad \\text{(conservative system)}',
      name: 'Conservation of Energy',
      domain: 'Classical Mechanics',
    },
  ],
  'Special Relativity': [
    {
      id: 'ax-sr-1',
      latex: '\\text{Laws of physics are the same in all inertial frames}',
      name: 'Principle of Relativity',
      domain: 'Special Relativity',
    },
    {
      id: 'ax-sr-2',
      latex: 'c = \\text{const in all inertial frames}',
      name: 'Constancy of Speed of Light',
      domain: 'Special Relativity',
    },
  ],
  Electromagnetism: [
    {
      id: 'ax-em-1',
      latex: '\\nabla \\cdot \\vec{E} = \\frac{\\rho}{\\epsilon_0}',
      name: "Gauss's Law",
      domain: 'Electromagnetism',
    },
    {
      id: 'ax-em-2',
      latex: '\\nabla \\cdot \\vec{B} = 0',
      name: "Gauss's Law for Magnetism",
      domain: 'Electromagnetism',
    },
    {
      id: 'ax-em-3',
      latex: '\\nabla \\times \\vec{E} = -\\frac{\\partial \\vec{B}}{\\partial t}',
      name: "Faraday's Law",
      domain: 'Electromagnetism',
    },
    {
      id: 'ax-em-4',
      latex:
        '\\nabla \\times \\vec{B} = \\mu_0 \\vec{J} + \\mu_0 \\epsilon_0 \\frac{\\partial \\vec{E}}{\\partial t}',
      name: "Ampere-Maxwell Law",
      domain: 'Electromagnetism',
    },
  ],
  'Quantum Mechanics': [
    {
      id: 'ax-qm-1',
      latex: 'i\\hbar \\frac{\\partial}{\\partial t}|\\Psi\\rangle = \\hat{H}|\\Psi\\rangle',
      name: "Schrodinger Equation",
      domain: 'Quantum Mechanics',
    },
    {
      id: 'ax-qm-2',
      latex: '\\langle\\Psi|\\Psi\\rangle = 1',
      name: 'Normalization',
      domain: 'Quantum Mechanics',
    },
    {
      id: 'ax-qm-3',
      latex: '[\\hat{x}, \\hat{p}] = i\\hbar',
      name: 'Canonical Commutation',
      domain: 'Quantum Mechanics',
    },
  ],
  Thermodynamics: [
    {
      id: 'ax-td-0',
      latex: 'T_A = T_B \\land T_B = T_C \\implies T_A = T_C',
      name: 'Zeroth Law',
      domain: 'Thermodynamics',
    },
    {
      id: 'ax-td-1',
      latex: '\\Delta U = Q - W',
      name: 'First Law',
      domain: 'Thermodynamics',
    },
    {
      id: 'ax-td-2',
      latex: '\\Delta S \\geq 0',
      name: 'Second Law',
      domain: 'Thermodynamics',
    },
    {
      id: 'ax-td-3',
      latex: '\\lim_{T \\to 0} S = 0',
      name: 'Third Law',
      domain: 'Thermodynamics',
    },
  ],
}

export const domainDescriptions: Record<
  string,
  { description: string; theoremCount: number }
> = {
  'Classical Mechanics': {
    description:
      'The study of motion of macroscopic objects under forces. Foundation of physics from Newton to Lagrange.',
    theoremCount: 45210,
  },
  Electromagnetism: {
    description:
      "Unified theory of electric and magnetic phenomena, governed by Maxwell's equations.",
    theoremCount: 62340,
  },
  'Special Relativity': {
    description:
      "Einstein's theory of space and time for inertial frames. Unifies mechanics and electrodynamics.",
    theoremCount: 38920,
  },
  'General Relativity': {
    description:
      'Geometric theory of gravitation describing spacetime curvature caused by mass and energy.',
    theoremCount: 29180,
  },
  'Quantum Mechanics': {
    description:
      'The fundamental theory of nature at atomic and subatomic scales, based on wave functions and operators.',
    theoremCount: 98450,
  },
  Thermodynamics: {
    description:
      'The science of heat, work, and energy transformations governed by the four laws.',
    theoremCount: 73191,
  },
}

export const mockTimelineEntries: Array<{
  id: string
  timestamp: string
  theorem: Theorem
  operator: string
}> = [
  {
    id: 'tl-1',
    timestamp: '2025-01-30T14:23:01Z',
    theorem: mockTheorems[0],
    operator: 'Crossover',
  },
  {
    id: 'tl-2',
    timestamp: '2025-01-30T14:22:48Z',
    theorem: mockTheorems[1],
    operator: 'Mutation',
  },
  {
    id: 'tl-3',
    timestamp: '2025-01-30T14:22:30Z',
    theorem: mockTheorems[2],
    operator: 'Crossover',
  },
  {
    id: 'tl-4',
    timestamp: '2025-01-30T14:22:15Z',
    theorem: mockTheorems[3],
    operator: 'Selection',
  },
  {
    id: 'tl-5',
    timestamp: '2025-01-30T14:21:58Z',
    theorem: mockTheorems[4],
    operator: 'Mutation',
  },
  {
    id: 'tl-6',
    timestamp: '2025-01-30T14:21:40Z',
    theorem: mockTheorems[5],
    operator: 'Crossover',
  },
  {
    id: 'tl-7',
    timestamp: '2025-01-30T14:21:22Z',
    theorem: mockTheorems[6],
    operator: 'Selection',
  },
  {
    id: 'tl-8',
    timestamp: '2025-01-30T14:21:05Z',
    theorem: mockTheorems[7],
    operator: 'Mutation',
  },
]
