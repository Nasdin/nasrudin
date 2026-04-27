import { useEffect, useState } from 'react';

interface CliLine {
  p: string;
  t: string;
  out?: boolean;
  ok?: boolean;
  dim?: boolean;
  high?: boolean;
}

const LINES: CliLine[] = [
  { p: '$', t: 'curl -L nasrudin.dev/install.sh | sh', out: false },
  { p: '', t: 'Installing nasrudin v0.4.2 · linux-x86_64', out: true, dim: true },
  {
    p: '',
    t: '✓ Rust 1.79 · ✓ Lean 4.10.0 · ✓ Mathlib snapshot 2026-04',
    out: true,
    ok: true,
  },
  { p: '', t: '✓ RocksDB store initialised at ~/.nasrudin/db', out: true, ok: true },
  { p: '$', t: 'nasrudin worker --register --pseudonym aklint', out: false },
  { p: '', t: '→ joined network as worker:home-pc-aklint', out: true, dim: true },
  { p: '$', t: 'nasrudin worker run --threads 8', out: false },
  {
    p: '',
    t: '[gen 1·001] mutate → ⟨ψ|ψ⟩ ≥ 0  · simp ✓  (0.04s)',
    out: true,
    ok: true,
  },
  {
    p: '',
    t: '[gen 1·002] crossover → tr(AB) = tr(BA) · ring ✓ (0.01s)',
    out: true,
    ok: true,
  },
  {
    p: '',
    t: '[gen 1·003] compose → ∇·B = 0 → ∮B·dA = 0 · ✓ (0.21s)',
    out: true,
    ok: true,
  },
  { p: '', t: '[gen 1·004] mutate → F = m²a · type mismatch ✗', out: true, dim: true },
  { p: '', t: 'uploading 3 verified to nasrudin.dev …', out: true, high: true },
];

export function InstallNode() {
  const [shown, setShown] = useState(2);
  useEffect(() => {
    const t = setInterval(() => setShown((s) => (s >= LINES.length ? 2 : s + 1)), 950);
    return () => clearInterval(t);
  }, []);

  return (
    <div className="install">
      <div className="install-cli">
        <div className="install-cli-bar">
          <div className="cli-dot" />
          <div className="cli-dot" />
          <div className="cli-dot" />
          <span className="cli-title">~/nasrudin · zsh</span>
        </div>
        <div className="install-cli-body">
          {LINES.slice(0, shown).map((l, i) => (
            <div key={`${i}-${l.t}`}>
              {l.p && <span className="prompt">{l.p}</span>}
              {l.p && ' '}
              <span className={l.ok ? 'ok' : l.dim ? 'dim' : l.high ? 'high' : l.out ? 'out' : ''}>
                {l.t}
              </span>
            </div>
          ))}
          {shown < LINES.length && <span className="cursor" />}
        </div>
      </div>
      <div className="install-side">
        <h3 className="h3" style={{ marginBottom: 8, fontSize: 24 }}>
          What you'll need
        </h3>
        <p style={{ marginBottom: 24, color: 'var(--ink-500)' }}>
          A modest desktop or cloud VM is enough. The harder you push, the faster physics arrives.
        </p>
        <ol className="install-reqs">
          <li>
            <span className="install-req-num">i.</span>
            <span className="install-req-name">
              CPU
              <span>4 cores minimum, 16+ recommended for serious throughput.</span>
            </span>
            <span className="install-req-val">x86_64 / arm64</span>
          </li>
          <li>
            <span className="install-req-num">ii.</span>
            <span className="install-req-name">
              Memory
              <span>Lean 4 likes RAM. The Mathlib snapshot wants room.</span>
            </span>
            <span className="install-req-val">≥ 8 GB</span>
          </li>
          <li>
            <span className="install-req-num">iii.</span>
            <span className="install-req-name">
              Disk
              <span>Local theorem store grows ~50 MB per million candidates.</span>
            </span>
            <span className="install-req-val">≥ 20 GB</span>
          </li>
          <li>
            <span className="install-req-num">iv.</span>
            <span className="install-req-name">
              Network
              <span>Workers POST batches to the central server every 60s.</span>
            </span>
            <span className="install-req-val">~5 MB/h</span>
          </li>
          <li>
            <span className="install-req-num">v.</span>
            <span className="install-req-name">
              Patience
              <span>Most candidates are nonsense. The wise fool knew this.</span>
            </span>
            <span className="install-req-val">∞</span>
          </li>
        </ol>
      </div>
    </div>
  );
}
