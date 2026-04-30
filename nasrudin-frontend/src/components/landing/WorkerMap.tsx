import { useWorkers } from '~/lib/queries';

const CITY_COORDS: Record<string, { x: number; y: number }> = {
  tokyo: { x: 620, y: 160 },
  berlin: { x: 432, y: 130 },
  austin: { x: 220, y: 165 },
  lagos: { x: 408, y: 220 },
  oslo: { x: 432, y: 100 },
  saopaulo: { x: 280, y: 290 },
  bengaluru: { x: 558, y: 215 },
  sydney: { x: 690, y: 320 },
  cairo: { x: 472, y: 180 },
  toronto: { x: 178, y: 145 },
  london: { x: 412, y: 145 },
  dubai: { x: 540, y: 195 },
};

type PinStatus = 'ok' | 'idle' | 'off';

interface Pin {
  x: number;
  y: number;
  status: PinStatus;
  label: string;
}

const LAND_DOTS: ReadonlyArray<{ x: number; y: number }> = (() => {
  const dots: { x: number; y: number }[] = [];
  for (let row = 0; row < 40; row++) {
    for (let col = 0; col < 80; col++) {
      const inLand =
        (col > 12 && col < 28 && row > 8 && row < 20) ||
        (col > 24 && col < 34 && row > 18 && row < 32) ||
        (col > 38 && col < 50 && row > 8 && row < 16) ||
        (col > 38 && col < 56 && row > 16 && row < 28) ||
        (col > 52 && col < 72 && row > 9 && row < 22) ||
        (col > 64 && col < 76 && row > 26 && row < 32);
      if (inLand) dots.push({ x: col * 10 + 5, y: row * 9 + 5 });
    }
  }
  return dots;
})();

export function WorkerMap() {
  const workers = useWorkers();
  const pins: Pin[] =
    workers.data
      ?.map<Pin | null>((w) => {
        const key = w.host?.toLowerCase().replace(/[^a-z]/g, '') ?? '';
        const coords = CITY_COORDS[key];
        if (!coords) return null;
        const status = String(w.status).toLowerCase();
        const pinStatus: PinStatus =
          status === 'active' ? 'ok' : status === 'inactive' ? 'idle' : 'off';
        return {
          x: coords.x,
          y: coords.y,
          status: pinStatus,
          label: w.host ?? w.id,
        };
      })
      .filter((p): p is Pin => p !== null) ?? [];

  return (
    <div className="network-grid">
      <div className="network-map">
        <div
          style={{
            display: 'flex',
            justifyContent: 'space-between',
            alignItems: 'baseline',
            marginBottom: 16,
          }}
        >
          <span className="overline">Active workers · last 60s</span>
          <span style={{ fontFamily: 'var(--font-mono)', fontSize: 12, color: 'var(--ink-500)' }}>
            {pins.length} pins · 6 continents
          </span>
        </div>
        <svg viewBox="0 0 800 360" width="100%" style={{ display: 'block' }}>
          <title>Distributed worker map</title>
          {/* dot-grid land mask */}
          {LAND_DOTS.map(({ x, y }) => (
            <circle key={`${x}-${y}`} cx={x} cy={y} r="1.1" fill="var(--paper-300)" />
          ))}
          {pins.map((p, i) => {
            const color =
              p.status === 'ok'
                ? 'var(--olive-500)'
                : p.status === 'idle'
                  ? 'var(--saffron-500)'
                  : 'var(--paper-300)';
            return (
              <g key={`${p.label}-${i}`}>
                {p.status === 'ok' && (
                  <circle cx={p.x} cy={p.y} r="4" fill={color} opacity="0.4">
                    <animate
                      attributeName="r"
                      values="4;18;4"
                      dur="3s"
                      repeatCount="indefinite"
                      begin={`${(i % 5) * 0.6}s`}
                    />
                    <animate
                      attributeName="opacity"
                      values="0.5;0;0.5"
                      dur="3s"
                      repeatCount="indefinite"
                      begin={`${(i % 5) * 0.6}s`}
                    />
                  </circle>
                )}
                <circle
                  cx={p.x}
                  cy={p.y}
                  r="3.2"
                  fill={color}
                  stroke="var(--paper-50)"
                  strokeWidth="1"
                />
                <text
                  x={p.x + 6}
                  y={p.y - 6}
                  fontSize="9"
                  fill="var(--ink-500)"
                  fontFamily="var(--font-mono)"
                >
                  {p.label}
                </text>
              </g>
            );
          })}
        </svg>
        <div
          style={{
            marginTop: 14,
            display: 'flex',
            gap: 18,
            fontSize: 11,
            color: 'var(--ink-500)',
            letterSpacing: '0.04em',
            textTransform: 'uppercase',
            fontWeight: 600,
          }}
        >
          <span style={{ display: 'inline-flex', alignItems: 'center', gap: 6 }}>
            <span
              style={{
                width: 7,
                height: 7,
                borderRadius: '50%',
                background: 'var(--olive-500)',
              }}
            />{' '}
            Active
          </span>
          <span style={{ display: 'inline-flex', alignItems: 'center', gap: 6 }}>
            <span
              style={{
                width: 7,
                height: 7,
                borderRadius: '50%',
                background: 'var(--saffron-500)',
              }}
            />{' '}
            Idle
          </span>
          <span style={{ display: 'inline-flex', alignItems: 'center', gap: 6 }}>
            <span
              style={{
                width: 7,
                height: 7,
                borderRadius: '50%',
                background: 'var(--paper-300)',
              }}
            />{' '}
            Offline
          </span>
        </div>
      </div>
      <div className="network-stats">
        <div className="network-stat-card">
          <div className="network-big-num">{(workers.data?.length ?? 0).toLocaleString()}</div>
          <div className="network-label">Workers · live</div>
        </div>
      </div>
    </div>
  );
}
