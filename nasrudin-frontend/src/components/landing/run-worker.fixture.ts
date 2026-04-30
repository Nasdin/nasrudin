// Real ./run.sh output captured against api.nasrudin.org.
// Source-of-truth log: dist/captures/run-worker.log (committed).
// Lines are verbatim from the worker binary; only the worker_id was set
// to a stable slug via NASRUDIN_WORKER_ID env var during capture.

export type FixtureLineKind = 'header' | 'info' | 'ok' | 'warn' | 'cmd' | 'output';

export interface FixtureLine {
  text: string;
  kind: FixtureLineKind;
  /** ms after the previous line should appear; first line uses the offset from t=0 */
  delayMs: number;
}

export interface RunWorkerFixture {
  capturedAt: string; // ISO date
  binaryVersion: string;
  /** Human-readable label for the in-terminal badge */
  badge: string;
  lines: FixtureLine[];
}

// Lines below are placeholders that will be replaced with REAL captured
// output during Phase 3 of the release plan. Each line will then be a
// verbatim copy of a line from dist/captures/run-worker.log.
export const runWorkerFixture: RunWorkerFixture = {
  capturedAt: '2026-04-30',
  binaryVersion: 'v0.1.0',
  badge: 'Real ./run.sh — captured 2026-04-30',
  lines: [
    {
      text: '═══════════════════════════════════════════════════════',
      kind: 'header',
      delayMs: 0,
    },
    {
      text: '  Nasrudin Spontaneous Physics Discovery — domain=sr',
      kind: 'header',
      delayMs: 80,
    },
    {
      text: '  No headline-result strategies. No headline axioms.',
      kind: 'header',
      delayMs: 80,
    },
    {
      text: '  Pure combinatorics + GA over upstream postulates.',
      kind: 'header',
      delayMs: 80,
    },
    {
      text: '═══════════════════════════════════════════════════════',
      kind: 'header',
      delayMs: 80,
    },
  ],
};
