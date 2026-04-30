import { Link } from '@tanstack/react-router';
import { useEffect, useMemo, useState } from 'react';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import { useRecentTheorems } from '~/lib/queries';

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

/** Render a real recent theorem as a "VERIFIED  thm:<id>  <statement>" ticker line. */
function tickerLineFor(t: {
  id: number[];
  latex?: string | null;
  canonical_statement?: string | null;
}): string {
  const id = bytesToHex(t.id).slice(0, 6);
  const stmt = (t.latex ?? t.canonical_statement ?? '').toString().slice(0, 80);
  return `VERIFIED  thm:${id}…  ${stmt}`;
}

export function HeroLiveTheorem() {
  const recent = useRecentTheorems(12);
  const [idx, setIdx] = useState(0);
  const [tickerLines, setTickerLines] = useState<string[]>([]);
  const [tickIdx, setTickIdx] = useState(0);

  // Shuffle theorems on load to avoid same order every render.
  const shuffledTheorems = useMemo(() => {
    if (!recent.data?.theorems) return [];
    const arr = [...recent.data.theorems];
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      const temp = arr[i];
      if (arr[j] !== undefined) arr[i] = arr[j];
      if (temp !== undefined) arr[j] = temp;
    }
    return arr;
  }, [recent.data?.theorems]);

  // Seed the ticker with REAL recent theorems as soon as the REST query lands.
  useEffect(() => {
    if (recent.data?.theorems?.length) {
      setTickerLines(recent.data.theorems.slice(0, 8).map(tickerLineFor));
    }
  }, [recent.data]);

  const total = shuffledTheorems.length;
  useEffect(() => {
    if (total === 0) return;
    const t = setInterval(() => setIdx((i) => (i + 1) % total), 5500);
    return () => clearInterval(t);
  }, [total]);

  // SSE subscription to /api/events/discoveries — prepends each verified theorem.
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
    if (tickerLines.length === 0) return;
    const t = setInterval(() => setTickIdx((i) => (i + 1) % tickerLines.length), 1800);
    return () => clearInterval(t);
  }, [tickerLines.length]);

  const t = shuffledTheorems[idx];
  const stmt = t?.latex ?? t?.canonical_statement;
  const id = t ? bytesToHex(t.id) : null;
  const domain = t?.domain;
  const generation = t?.generation;
  const verifiedAt = t?.verified_at ? new Date(t.verified_at) : null;
  const timeAgo = verifiedAt ? getTimeAgo(verifiedAt) : null;

  // No real theorem yet → skeleton card. Never invent one.
  if (!t || !id || !stmt) {
    return (
      <div>
        <div className="theorem-card theorem-card-loading" aria-live="polite">
          <div className="theorem-card-head">
            <span className="theorem-card-id" style={{ opacity: 0.4 }}>
              thm:…
            </span>
            <span className="verified-badge">
              <span className="verified-dot" /> waiting for live events…
            </span>
          </div>
          <div className="theorem-card-body">
            <div className="theorem-statement" style={{ opacity: 0.4 }}>
              —
            </div>
            <div className="theorem-name" style={{ opacity: 0.4 }}>
              &nbsp;
            </div>
            <div className="theorem-tag" style={{ opacity: 0.4 }}>
              connecting…
            </div>
          </div>
        </div>
        <div className="ticker">
          <span className="ticker-label">Live</span>
          <span className="ticker-text" style={{ color: 'var(--ink-500)' }}>
            waiting for live events…
          </span>
        </div>
      </div>
    );
  }

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
            {tickerLines[tickIdx] ?? 'waiting for live events…'}
          </span>
        </span>
      </div>
    </div>
  );
}
