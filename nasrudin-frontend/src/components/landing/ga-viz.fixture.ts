// Real GA-cycle trace captured against api.nasrudin.org.
// Source-of-truth log: dist/captures/ga-trace.log (committed).
// Lines are verbatim from the worker's GA output.

export interface GaRow {
  /** GA operation: 'axiom' = seed; otherwise one of mutate / crossover / compose. */
  op: 'axiom' | 'mutate' | 'crossover' | 'compose';
  expr: string;
  status: 'seed' | 'accepted' | 'rejected';
  /** Right-aligned annotation such as "verified · 0.4s" or "type mismatch". */
  result: string;
}

export interface GaVizFixture {
  capturedAt: string | null;
  workerId: string | null;
  /** Generation index of the FIRST row below — subsequent rows share the same generation. */
  generationStart: number | null;
  rows: GaRow[];
}

// Empty by default — populated in Phase 3 of the release plan with REAL
// captured GA cycles from running the worker against api.nasrudin.org.
// Until then, GAViz renders a "captured trace pending" honest placeholder.
export const gaVizFixture: GaVizFixture = {
  capturedAt: null,
  workerId: null,
  generationStart: null,
  rows: [],
};
