import { useEffect, useState } from 'react';
import { gaVizFixture } from './ga-viz.fixture';

export function GAViz() {
  const { rows, workerId, generationStart, capturedAt } = gaVizFixture;
  const [gen, setGen] = useState(0);

  useEffect(() => {
    if (rows.length === 0) return;
    const t = setInterval(() => setGen((g) => (g + 1) % rows.length), 1400);
    return () => clearInterval(t);
  }, [rows.length]);

  if (rows.length === 0) {
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
              Captured trace pending
            </div>
            <div
              style={{
                fontFamily: 'var(--font-serif)',
                fontSize: 22,
                fontStyle: 'italic',
                color: 'var(--ink-500)',
              }}
            >
              A real GA cycle will land here once the v0.1.0 worker has been captured against the
              live network.
            </div>
          </div>
        </div>
      </div>
    );
  }

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
            Generation {generationStart?.toLocaleString() ?? '—'} · captured trace
          </div>
          <div
            style={{
              fontFamily: 'var(--font-serif)',
              fontSize: 22,
              fontStyle: 'italic',
              color: 'var(--ink-700)',
            }}
          >
            Real GA cycle from a worker run on {capturedAt ?? 'an undated capture'}.
          </div>
        </div>
        <div style={{ fontFamily: 'var(--font-mono)', fontSize: 12, color: 'var(--ink-500)' }}>
          worker · {workerId ?? 'unknown'}
        </div>
      </div>
      <div className="ga-rows">
        {rows.map((row, i) => {
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
