import { describe, expect, it } from 'vitest';
import {
  buildSteeringPayload,
  emptySteeringForm,
  hasAnySteering,
  prettyDomainKey,
  prettyOperatorName,
  type SteeringFormState,
} from './steering';

describe('hasAnySteering', () => {
  it('returns false for a fresh empty form', () => {
    expect(hasAnySteering(emptySteeringForm())).toBe(false);
  });

  it('returns true once a single atom weight is set', () => {
    const s: SteeringFormState = {
      ...emptySteeringForm(),
      atomPool: { special_relativity: { m_c_sq: 3.0 } },
    };
    expect(hasAnySteering(s)).toBe(true);
  });

  it('returns true once a single mutation knob is set', () => {
    const s: SteeringFormState = {
      ...emptySteeringForm(),
      mutationKnobs: { rate: 0.15 },
    };
    expect(hasAnySteering(s)).toBe(true);
  });

  it('returns true once an operator prior is set', () => {
    const s: SteeringFormState = {
      ...emptySteeringForm(),
      mutationPriors: { append_productive_suffix: 1.8 },
    };
    expect(hasAnySteering(s)).toBe(true);
  });

  it('treats an empty per-domain atom map as no-steering', () => {
    // The disclosure may select a domain without picking any atoms;
    // that should NOT trigger the surcharge.
    const s: SteeringFormState = {
      ...emptySteeringForm(),
      atomPool: { special_relativity: {} },
    };
    expect(hasAnySteering(s)).toBe(false);
  });
});

describe('buildSteeringPayload', () => {
  it('returns undefined for empty state', () => {
    expect(buildSteeringPayload(emptySteeringForm())).toBeUndefined();
  });

  it('emits only the fields that were set', () => {
    const s: SteeringFormState = {
      atomPool: { special_relativity: { m_c_sq: 4.0, c_sq: 2.0 } },
      mutationPriors: { append_productive_suffix: 2.0 },
      mutationKnobs: { rate: 0.2, populationSize: 128 },
    };
    const out = buildSteeringPayload(s);
    expect(out).toBeDefined();
    expect(out?.mutation_knobs).toEqual({ rate: 0.2, population_size: 128 });
    expect(out?.mutation_priors).toEqual({ append_productive_suffix: 2.0 });
    expect(out?.atom_pool?.special_relativity).toEqual([
      { name: 'm_c_sq', weight: 4.0 },
      { name: 'c_sq', weight: 2.0 },
    ]);
  });

  it('omits sub-objects entirely when they have no entries', () => {
    const s: SteeringFormState = {
      ...emptySteeringForm(),
      mutationKnobs: { suffixBias: 0.6 },
    };
    const out = buildSteeringPayload(s);
    expect(out).toEqual({ mutation_knobs: { suffix_bias: 0.6 } });
    expect(out?.mutation_priors).toBeUndefined();
    expect(out?.atom_pool).toBeUndefined();
  });

  it('drops domains whose atom map is empty', () => {
    const s: SteeringFormState = {
      ...emptySteeringForm(),
      atomPool: { special_relativity: { m_c_sq: 1.0 }, electromagnetism: {} },
    };
    const out = buildSteeringPayload(s);
    expect(out?.atom_pool).toEqual({
      special_relativity: [{ name: 'm_c_sq', weight: 1.0 }],
    });
  });

  it('snake_cases the knob keys to match the backend schema', () => {
    const s: SteeringFormState = {
      ...emptySteeringForm(),
      mutationKnobs: {
        rate: 0.1,
        populationSize: 256,
        suffixBias: 0.5,
        elitismFraction: 0.05,
      },
    };
    const out = buildSteeringPayload(s);
    expect(out?.mutation_knobs).toEqual({
      rate: 0.1,
      population_size: 256,
      suffix_bias: 0.5,
      elitism_fraction: 0.05,
    });
  });
});

describe('prettyDomainKey', () => {
  it('title-cases the snake-case domain key', () => {
    expect(prettyDomainKey('special_relativity')).toBe('Special Relativity');
    expect(prettyDomainKey('pure_math')).toBe('Pure Math');
  });
});

describe('prettyOperatorName', () => {
  it('replaces underscores with spaces', () => {
    expect(prettyOperatorName('append_productive_suffix')).toBe('append productive suffix');
  });
});
