import { useEffect, useState } from 'react';

const GA_GENERATIONS = [
  { op: 'axiom', expr: '∂L/∂q̇ = p', status: 'seed', result: 'from postulate' },
  { op: 'axiom', expr: 'L = T − V', status: 'seed', result: 'from postulate' },
  { op: 'mutate', expr: 'dp/dt = ∂L/∂q', status: 'accepted', result: 'verified · 0.4s' },
  { op: 'crossover', expr: 'dp/dt = −∂V/∂q', status: 'accepted', result: 'verified · 1.1s' },
  { op: 'mutate', expr: 'F = dp/dt', status: 'accepted', result: 'verified · 0.2s' },
  { op: 'compose', expr: 'F = ma', status: 'accepted', result: 'Newton II — verified' },
  { op: 'mutate', expr: 'F = m²a', status: 'rejected', result: 'type mismatch' },
  { op: 'crossover', expr: 'p² = 2mE', status: 'accepted', result: 'verified · 0.6s' },
];

export function GAViz() {
  const [gen, setGen] = useState(0);
  useEffect(() => {
    const t = setInterval(() => setGen((g) => (g + 1) % GA_GENERATIONS.length), 1400);
    return () => clearInterval(t);
  }, []);

  return (
    <div className="ga-viz">
      <div
        style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'baseline',
          marginBottom: 20,
        }}
      >
        <div>
          <div className="overline" style={{ marginBottom: 6 }}>
            Generation 4,218,107 · live trace
          </div>
          <div
            style={{
              fontFamily: 'var(--font-serif)',
              fontSize: 22,
              fontStyle: 'italic',
              color: 'var(--ink-700)',
            }}
          >
            From the lagrangian axioms, two crossovers and three mutations later — Newton's second
            law.
          </div>
        </div>
        <div style={{ fontFamily: 'var(--font-mono)', fontSize: 12, color: 'var(--ink-500)' }}>
          worker · home-pc-aklint
        </div>
      </div>
      <div className="ga-rows">
        {GA_GENERATIONS.map((row, i) => {
          const visible = i <= gen;
          const cls =
            row.status === 'accepted' ? 'accepted' : row.status === 'rejected' ? 'rejected' : '';
          return (
            <div
              className={`ga-row ${cls}`}
              key={`${row.op}-${row.expr}`}
              style={{
                opacity: visible ? (cls === 'rejected' ? 0.45 : 1) : 0.18,
                transition: 'opacity .6s',
              }}
            >
              <span className="ga-op">{row.op}</span>
              <span className="ga-expr">{row.expr}</span>
              <span
                className={`ga-result ${
                  row.status === 'accepted' ? 'ok' : row.status === 'rejected' ? 'no' : ''
                }`}
              >
                {row.result}
              </span>
            </div>
          );
        })}
      </div>
    </div>
  );
}
