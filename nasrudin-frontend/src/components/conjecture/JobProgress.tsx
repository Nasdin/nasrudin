import type { ConjectureSseEvent, ConjectureView } from '~/lib/types';

export function JobProgress({
  view,
  events,
}: {
  view: ConjectureView;
  events: ConjectureSseEvent[];
}) {
  return (
    <div className="card" style={{ marginTop: 24 }}>
      <h3 className="section-h" style={{ fontSize: 22, marginBottom: 16 }}>
        Live progress
      </h3>
      <div
        style={{
          display: 'grid',
          gridTemplateColumns: '1fr 1fr',
          gap: 16,
          fontFamily: 'var(--font-mono)',
        }}
      >
        <div>
          <div style={{ color: 'var(--ink-500)', fontSize: 12 }}>state</div>
          <div style={{ fontSize: 18 }}>{view.state}</div>
        </div>
        <div>
          <div style={{ color: 'var(--ink-500)', fontSize: 12 }}>candidates</div>
          <div style={{ fontSize: 18 }}>
            {view.candidates_attempted.toLocaleString()} attempted ·{' '}
            {view.candidates_verified.toLocaleString()} verified
          </div>
        </div>
      </div>
      <div style={{ marginTop: 24 }}>
        <div style={{ color: 'var(--ink-500)', fontSize: 12, marginBottom: 8 }}>event log</div>
        {events.length === 0 ? (
          <div style={{ color: 'var(--ink-500)', fontSize: 13 }}>
            (waiting for the first event…)
          </div>
        ) : (
          <ul
            style={{
              listStyle: 'none',
              padding: 0,
              margin: 0,
              maxHeight: 320,
              overflowY: 'auto',
              fontFamily: 'var(--font-mono)',
              fontSize: 13,
            }}
          >
            {events.map((e) => (
              <li
                key={e.id}
                style={{
                  borderTop: '1px solid var(--paper-200)',
                  padding: '6px 0',
                }}
              >
                <span style={{ color: 'var(--ink-500)' }}>
                  {new Date(e.at).toLocaleTimeString()}
                </span>{' '}
                <strong>{e.kind}</strong>{' '}
                <code style={{ fontSize: 12, color: 'var(--ink-700)' }}>
                  {JSON.stringify(e.payload)}
                </code>
              </li>
            ))}
          </ul>
        )}
      </div>
    </div>
  );
}
