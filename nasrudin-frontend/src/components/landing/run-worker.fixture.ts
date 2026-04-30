// Real ./run.sh output captured 2026-04-30 against api.nasrudin.org with a
// worker bundled in worker-v0.1.0. Source-of-truth log:
// deploy/captures/run-worker.log (committed). Lines below are VERBATIM
// from that capture; only the worker_id was set to a stable slug
// ("capture-2026-04-30") via NASRUDIN_WORKER_ID. The capture stops just
// before the first chunk-submit so the replay reflects steady-state
// behaviour rather than the prod-side ingest issue we hit during capture
// (separate bug).

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

export const runWorkerFixture: RunWorkerFixture = {
  capturedAt: '2026-04-30',
  binaryVersion: 'v0.1.0',
  badge: 'Real ./run.sh — captured 2026-04-30',
  lines: [
    { text: '[worker] first run: warming Mathlib cache (this takes a few minutes)...', kind: 'cmd', delayMs: 0 },
    { text: '[worker] api=https://api.nasrudin.org  id=capture-2026-04-30',           kind: 'info', delayMs: 600 },
    { text: '═══════════════════════════════════════════════════════', kind: 'header', delayMs: 600 },
    { text: '  Nasrudin Spontaneous Physics Discovery — domain=sr',     kind: 'header', delayMs: 60 },
    { text: '  No headline-result strategies. No headline axioms.',     kind: 'header', delayMs: 60 },
    { text: '  Pure combinatorics + GA over upstream postulates.',      kind: 'header', delayMs: 60 },
    { text: '═══════════════════════════════════════════════════════', kind: 'header', delayMs: 60 },
    { text: '',                                                          kind: 'output', delayMs: 200 },
    { text: '▶ API submission target: https://api.nasrudin.org',         kind: 'cmd',    delayMs: 200 },
    { text: '    worker_id: capture-2026-04-30',                         kind: 'info',   delayMs: 100 },
    { text: '',                                                          kind: 'output', delayMs: 200 },
    { text: '▶ Upstream axiom set (16 axioms):',                         kind: 'cmd',    delayMs: 250 },
    { text: '    • rest_frame_psq_zero',                                 kind: 'output', delayMs: 70 },
    { text: '    • velocity_def',                                        kind: 'output', delayMs: 70 },
    { text: '    • kinetic_energy_def',                                  kind: 'output', delayMs: 70 },
    { text: '    • gravitational_force',                                 kind: 'output', delayMs: 70 },
    { text: '    • acceleration_def',                                    kind: 'output', delayMs: 70 },
    { text: '    • four_momentum_time_component',                        kind: 'output', delayMs: 70 },
    { text: '    • energy_nonneg',                                       kind: 'output', delayMs: 70 },
    { text: '    • mass_nonneg',                                         kind: 'output', delayMs: 70 },
    { text: '    • newton_second_dpdt',                                  kind: 'output', delayMs: 70 },
    { text: '    • momentum_def',                                        kind: 'output', delayMs: 70 },
    { text: '    • invariant_mass_postulate',                            kind: 'output', delayMs: 70 },
    { text: '    • power_def',                                           kind: 'output', delayMs: 70 },
    { text: '    • newton_second',                                       kind: 'output', delayMs: 70 },
    { text: '    • work_def',                                            kind: 'output', delayMs: 70 },
    { text: '    • c_positive',                                          kind: 'output', delayMs: 70 },
    { text: '    • minkowski_invariant_def',                             kind: 'output', delayMs: 70 },
    { text: '',                                                          kind: 'output', delayMs: 200 },
    { text: '  ✓ mass_shell_condition is NOT in the store. No cheating.', kind: 'ok',    delayMs: 250 },
    { text: '  ✓ no-cheat canonical-form audit passed',                  kind: 'ok',     delayMs: 250 },
    { text: '',                                                          kind: 'output', delayMs: 200 },
    { text: '▶ Target: sr_rest_energy (ladder of 3 rungs)',              kind: 'cmd',    delayMs: 300 },
    { text: '▶ Negative-result memo: 0 pre-rejected canonicals will be skipped', kind: 'cmd', delayMs: 200 },
    { text: '',                                                          kind: 'output', delayMs: 200 },
    { text: '▶ Dimension hard-reject ON (6 known vars; pass --soft-dimension to disable)', kind: 'cmd', delayMs: 250 },
    { text: '▶ Spawning persistent Lean elaborator (cwd=./prover, script=scripts/nasrudin_server.lean)', kind: 'cmd', delayMs: 250 },
    { text: '    ! elaborator failed to boot: server closed stdout before boot ack', kind: 'warn', delayMs: 1200 },
    { text: '    falling back to lake build (slow path)',                kind: 'output', delayMs: 200 },
    { text: '▶ Running discovery: pop=16, gens=3 (4 chunks × 1 gens), max_chain_len=12, lake_budget=2', kind: 'cmd', delayMs: 400 },
    { text: '',                                                          kind: 'output', delayMs: 200 },
    { text: '▶ ResourceBudget: 14 cores, 24576 MiB RAM → lake_slots=6, pop=32, gens=5000, chunks=12, max_lake/chunk=18', kind: 'info', delayMs: 300 },
    { text: '▶ chunk 1/4: 1 verified, 1 lake attempts',                  kind: 'ok',     delayMs: 800 },
    { text: '▶ chunk 2/4: 1 verified, 1 lake attempts',                  kind: 'ok',     delayMs: 800 },
  ],
};
