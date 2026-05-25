import { Link } from '@tanstack/react-router';
import { memo, useEffect, useMemo, useState } from 'react';
import { API_BASE } from '~/lib/api';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import { useRecentTheorems } from '~/lib/queries';
import { statementToLatex } from '~/lib/statementToLatex';

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

// Imported PhysLean / Mathlib rows carry the original Lean qualifier in
// `origin_payload.Imported.source`. When `latex` is null (true for every
// imported row), we use the qualifier as the headline instead of feeding
// the raw S-expression into KaTeX — KaTeX renders that as garbled
// "math" because the prefix-form `(pi v:Nat (...))` looks like
// concatenated identifiers, not algebra.
function importedSource(payload: unknown): string | null {
  if (payload == null || typeof payload !== 'object') return null;
  const obj = payload as Record<string, unknown>;
  const inner = obj.Imported as Record<string, unknown> | undefined;
  if (!inner) return null;
  const src = inner.source;
  return typeof src === 'string' ? src : null;
}

import { displayLeanName as lastSegment } from '~/lib/leanNames';

// Render the statement of a live-ticker theorem with KaTeX whenever
// possible — preferring server-side `latex`, then a client-side translation
// of the prefix-form `canonical_statement`, and finally falling back to the
// Lean qualifier (for imports with no statement at all). The previous
// fallback fed the raw S-expression through KaTeX, which produced unreadable
// concatenated-italic-letters output the user flagged as "not in latex".
function HeroStatement({
  latex,
  canonical,
  importedFrom,
}: {
  latex: string | null;
  canonical: string;
  importedFrom: string | null;
}) {
  const src = latex ?? statementToLatex(canonical).latex;
  if (src && src.trim().length > 0) {
    return (
      <div className="theorem-statement">
        <MathExpr source={src} block />
      </div>
    );
  }
  if (importedFrom) {
    return (
      <div
        className="theorem-statement"
        style={{
          fontFamily: 'var(--font-mono)',
          fontSize: 18,
          fontWeight: 600,
          textAlign: 'left',
          wordBreak: 'break-word',
        }}
        title={importedFrom}
      >
        {lastSegment(importedFrom)}
        <div
          style={{
            fontFamily: 'var(--font-mono)',
            fontSize: 11,
            fontWeight: 400,
            color: 'var(--ink-500)',
            marginTop: 6,
            wordBreak: 'break-all',
          }}
        >
          {importedFrom}
        </div>
      </div>
    );
  }
  return (
    <div className="theorem-statement" style={{ color: 'var(--ink-500)', fontStyle: 'italic' }}>
      (no statement)
    </div>
  );
}

/** Render a real recent theorem as a "VERIFIED  thm:<id>  <statement>" ticker line. */
function tickerLineFor(t: {
  id: number[];
  latex?: string | null;
  canonical_statement?: string | null;
  origin_payload?: unknown;
}): string {
  const id = bytesToHex(t.id).slice(0, 6);
  // Ticker line is one-line text: prefer the Lean qualifier for imports,
  // then latex, then a truncated canonical-statement preview. KaTeX is
  // not involved here so the raw text just needs to be short and human-
  // readable.
  const imp = importedSource(t.origin_payload);
  const stmt = (t.latex ?? (imp ? lastSegment(imp) : t.canonical_statement) ?? '')
    .toString()
    .slice(0, 80);
  return `VERIFIED  thm:${id}…  ${stmt}`;
}

export const HeroLiveTheorem = memo(function HeroLiveTheorem() {
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
    const url = `${API_BASE}/api/events/discoveries`;
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
  const id = t ? bytesToHex(t.id) : null;
  const domain = t?.domain;
  const generation = t?.generation;
  const verifiedAt = t?.verified_at ? new Date(t.verified_at) : null;
  const timeAgo = verifiedAt ? getTimeAgo(verifiedAt) : null;
  const importedFrom = t ? importedSource(t.origin_payload) : null;
  // Display priority: real latex → headlined Lean qualifier (imports) →
  // truncated canonical preview. The old code fed the s-expression into
  // KaTeX which is what produced the (pidv:Nat(piv... output the user
  // flagged.
  const hasContent = !!t && !!id && (!!t.latex || !!importedFrom || !!t.canonical_statement);

  // No real theorem yet → skeleton card. Never invent one.
  if (!t || !id || !hasContent) {
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
            <HeroStatement
              latex={t.latex ?? null}
              canonical={t.canonical_statement ?? ''}
              importedFrom={importedFrom}
            />
            <div className="theorem-name">{id}</div>
            <div className="theorem-tag">
              {domain} · gen {generation}
              {timeAgo && <span> · {timeAgo}</span>}
              {importedFrom && <span> · imported</span>}
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
});
