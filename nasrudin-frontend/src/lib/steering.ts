// Helpers for the /research submit form's "Advanced steering" disclosure.
//
// `buildSteeringPayload` collapses the form-state into the exact shape
// `validate_and_canonicalize_steering` expects on the backend
// (`engine/crates/api/src/handlers/research_jobs.rs`). The contract is:
//
//   - empty sub-objects must be omitted entirely (otherwise the server
//     400s with "steering is present but contains no recognised fields"
//     once it strips empties),
//   - `atom_pool[domain]` must only carry entries whose name is in
//     `PHYSICS_ATOM_NAMES`,
//   - `mutation_knobs` only carries the keys actually set,
//   - if NOTHING is set, return `undefined` so the request omits the
//     `steering` field altogether and avoids the +1 credit surcharge.
//
// Keeping this logic on a plain helper (instead of inlined in the form)
// lets us unit-test it without rendering anything.

import type { AtomPool, MutationPriors, ResearchJobSteering, ResearchMutationKnobs } from './types';

export interface SteeringFormState {
  /** Per-domain → name → weight. UI uses nested maps so toggling an
   *  atom keeps the rest of the state stable. */
  atomPool: Record<string, Record<string, number>>;
  /** operator name → weight in [0, 2]. Entries with weight === undefined
   *  are skipped. */
  mutationPriors: Record<string, number | undefined>;
  /** Each knob is optional — only set fields land in the payload. */
  mutationKnobs: {
    rate?: number;
    populationSize?: number;
    suffixBias?: number;
    elitismFraction?: number;
  };
}

export function emptySteeringForm(): SteeringFormState {
  return {
    atomPool: {},
    mutationPriors: {},
    mutationKnobs: {},
  };
}

/**
 * True iff the form carries *any* user-set knob. Drives:
 *   - the "+1 credit (steering surcharge)" line in the cost preview,
 *   - whether to attach `steering` to the POST body at all.
 */
export function hasAnySteering(s: SteeringFormState): boolean {
  for (const [, atoms] of Object.entries(s.atomPool)) {
    if (Object.keys(atoms).length > 0) return true;
  }
  for (const v of Object.values(s.mutationPriors)) {
    if (typeof v === 'number') return true;
  }
  const k = s.mutationKnobs;
  if (typeof k.rate === 'number') return true;
  if (typeof k.populationSize === 'number') return true;
  if (typeof k.suffixBias === 'number') return true;
  if (typeof k.elitismFraction === 'number') return true;
  return false;
}

/**
 * Translate UI form-state → wire payload. Returns `undefined` when the
 * form is empty so the caller can decide whether to send `steering` at
 * all (and avoid the +1 credit surcharge).
 */
export function buildSteeringPayload(s: SteeringFormState): ResearchJobSteering | undefined {
  if (!hasAnySteering(s)) return undefined;

  const out: ResearchJobSteering = {};

  const knobs: ResearchMutationKnobs = {};
  if (typeof s.mutationKnobs.rate === 'number') knobs.rate = s.mutationKnobs.rate;
  if (typeof s.mutationKnobs.populationSize === 'number') {
    knobs.population_size = s.mutationKnobs.populationSize;
  }
  if (typeof s.mutationKnobs.suffixBias === 'number') {
    knobs.suffix_bias = s.mutationKnobs.suffixBias;
  }
  if (typeof s.mutationKnobs.elitismFraction === 'number') {
    knobs.elitism_fraction = s.mutationKnobs.elitismFraction;
  }
  if (Object.keys(knobs).length > 0) out.mutation_knobs = knobs;

  const priors: MutationPriors = {};
  for (const [op, w] of Object.entries(s.mutationPriors)) {
    if (typeof w === 'number') priors[op] = w;
  }
  if (Object.keys(priors).length > 0) out.mutation_priors = priors;

  const pool: AtomPool = {};
  for (const [domain, atoms] of Object.entries(s.atomPool)) {
    const entries = Object.entries(atoms)
      .filter(([, w]) => typeof w === 'number')
      .map(([name, weight]) => ({ name, weight }));
    if (entries.length > 0) pool[domain] = entries;
  }
  if (Object.keys(pool).length > 0) out.atom_pool = pool;

  // `hasAnySteering` already guarantees at least one branch fires, so
  // `out` is non-empty here.
  return out;
}

/** Pretty-print a snake_case domain key for the disclosure heading. */
export function prettyDomainKey(key: string): string {
  return key
    .split('_')
    .map((w) => w.charAt(0).toUpperCase() + w.slice(1))
    .join(' ');
}

/** Pretty-print a GA operator name for the prior-slider label. */
export function prettyOperatorName(name: string): string {
  return name.replace(/_/g, ' ');
}
