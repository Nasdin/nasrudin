import { useEffect, useState, useMemo } from 'react';
import { Link } from '@tanstack/react-router';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import { useRecentTheorems } from '~/lib/queries';

const FALLBACK_TICKER = [
  'VERIFIED  thm:9f3a2c   ⟨x,y⟩² ≤ ⟨x,x⟩⟨y,y⟩   simp ∘ linarith',
  'REJECTED  cand:7b41f8   simp made no progress; goal unchanged',
  'VERIFIED  thm:c1d9e7   [x,p] = iℏ                ring ∘ exact',
  'VERIFIED  thm:e88f01   tr(AB) = tr(BA)            Matrix.trace_mul_comm',
  'REJECTED  cand:9f0021   timeout after 30s on goal: NormedSpace ℝ E',
  'VERIFIED  thm:bb27d3   ⟨ψ|ψ⟩ ≥ 0                 inner_self_nonneg',
];

const FALLBACK_HERO = {
  id: 'thm:0000000000000000',
  domain: 'Inner product space',
  generation: 0,
  statement_latex: '|\\langle x,y\\rangle|^2 \\le \\langle x,x\\rangle \\langle y,y\\rangle',
  name: 'Schwarz inequality',
};

function getTimeAgo(date: Date): string {
  const seconds = Math.floor((Date.now() - date.getTime()) / 1000);
  if (seconds < 60) return 'just now';
  const minutes = Math.floor(seconds / 60);
  if (minutes < 60) return `${minutes}m ago`;
  const hours = Math.floor(minutes / 60);
  if (hours < 24) return `${hours}h ago`;
  const days = Math.floor(hours / 24);
  return `${days}d ago`;
}

export function HeroLiveTheorem() {
  const recent = useRecentTheorems(12);
  const [idx, setIdx] = useState(0);
  const [tickerLines, setTickerLines] = useState<string[]>(FALLBACK_TICKER);
  const [tickIdx, setTickIdx] = useState(0);

  // Shuffle theorems on load to avoid same order every time
  const shuffledTheorems = useMemo(() => {
    if (!recent.data?.theorems) return [];
    const arr = [...recent.data.theorems];
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      const temp = arr[i];
      if (arr[j] !== undefined) {
        arr[i] = arr[j];
      }
      if (temp !== undefined) {
        arr[j] = temp;
      }
    }
    return arr;
  }, [recent.data?.theorems]);

  const total = shuffledTheorems.length ?? 1;
  useEffect(() => {
    const t = setInterval(() => setIdx((i) => (i + 1) % Math.max(total, 1)), 5500);
    return () => clearInterval(t);
  }, [total]);

  // SSE subscription to /api/events/discoveries — falls back silently on errors.
  useEffect(() => {
    if (typeof window === 'undefined') return;
    let failures = 0;
    const url = `${import.meta.env.VITE_API_URL ?? 'http://localhost:3001'}/api/events/discoveries`;
    let es: EventSource | null;
    try {
      es = new EventSource(url, { withCredentials: true });
    } catch {
      return;
    }
    es.onmessage = (ev) => {
      const t = (() => {
        try {
          return JSON.parse(ev.data);
        } catch {
          return null;
        }
      })();
      // SSE `theorem_*` events carry a hex-encoded `theorem_id`, not a full
      // theorem object — see `nasrudin_api::reverify::DiscoveryEvent`.
      if (t && typeof t === 'object' && 'theorem_id' in t) {
        const ti = t as { theorem_id: string };
        setTickerLines((prev) =>
          [`VERIFIED  thm:${ti.theorem_id.slice(0, 6)}…`, ...prev].slice(0, 12),
        );
      }
    };
    es.onerror = () => {
      failures += 1;
      if (failures >= 3) es?.close();
    };
    return () => es?.close();
  }, []);

  useEffect(() => {
    const t = setInterval(() => setTickIdx((i) => (i + 1) % tickerLines.length), 1800);
    return () => clearInterval(t);
  }, [tickerLines.length]);

  const t = shuffledTheorems[idx];
  const stmt = t ? (t.latex ?? t.canonical_statement) : FALLBACK_HERO.statement_latex;
  const id = t ? bytesToHex(t.id) : FALLBACK_HERO.id;
  const domain = t?.domain ?? FALLBACK_HERO.domain;
  const generation = t?.generation ?? FALLBACK_HERO.generation;
  const verifiedAt = t?.verified_at ? new Date(t.verified_at) : null;
  const timeAgo = verifiedAt
    ? getTimeAgo(verifiedAt)
    : null;

  return (
    <div>
      <Link to="/theorem/$id" params={{ id }} className="theorem-card-link">
        <div className="theorem-card">
          <div className="theorem-card-head">
            <span className="theorem-card-id">{id.slice(0, 8)}</span>
            <span className="verified-badge">
              <span className="verified-dot" /> Verified · Lean 4
            </span>
          </div>
          <div className="theorem-card-body">
            <div className="theorem-statement">
              <MathExpr source={stmt} block />
            </div>
            <div className="theorem-name">{id}</div>
            <div className="theorem-tag">
              {domain} · gen {generation}
              {timeAgo && <span> · {timeAgo}</span>}
            </div>
          </div>
        </div>
      </Link>
      <div className="ticker">
        <span className="ticker-label">Live</span>
        <span className="ticker-text" key={tickIdx}>
          <span className={tickerLines[tickIdx]?.startsWith('VERIFIED') ? 'ok' : 'reject'}>
            {tickerLines[tickIdx]}
          </span>
        </span>
      </div>
    </div>
  );
}
