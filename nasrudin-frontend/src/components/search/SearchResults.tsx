import { Link } from '@tanstack/react-router';
import { memo } from 'react';
import { Math as MathExpr } from '~/lib/katex';
import type { SearchMatchItem, SearchTier } from '~/lib/types';
import { MatchBadge } from './MatchBadge';

interface Props {
  tier: SearchTier;
  matches: SearchMatchItem[];
  tookMs: number;
}

const TIER_HEADLINE: Record<SearchTier, string> = {
  exact: 'Exact match — your conjecture is already proven',
  unify: 'Pattern matched in the corpus',
  near_miss: 'No exact hit; closest theorems by structural distance',
  empty: 'No matches',
};

export function SearchResults({ tier, matches, tookMs }: Props) {
  return (
    <div style={containerStyle}>
      <div style={headerStyle}>
        <h2 style={headlineStyle}>{TIER_HEADLINE[tier]}</h2>
        <span style={metaStyle}>
          {matches.length} result{matches.length === 1 ? '' : 's'} · {tookMs} ms
        </span>
      </div>
      {matches.map((m) => (
        <Result key={m.id} m={m} />
      ))}
    </div>
  );
}

const Result = memo(function Result({ m }: { m: SearchMatchItem }) {
  const stmt = m.statement_latex ?? m.canonical_statement;
  return (
    <div className="result-card" style={cardStyle}>
      <div style={resultGridStyle}>
        <Link
          to="/theorem/$id"
          params={{ id: m.id }}
          style={resultLinkStyle}
        >
          <div className="result-stmt">
            <MathExpr source={stmt} />
          </div>
        </Link>
        <div className="result-meta" style={resultMetaStyle}>
          <MatchBadge kind={m.match} />
          <span style={monoSmallStyle}>thm:{m.id.slice(0, 8)}</span>
          <span className="dot">·</span>
          <span style={domainSmallStyle}>{m.domain}</span>
          <span className="dot">·</span>
          <span style={depthStyle}>depth {m.depth ?? 0}</span>
        </div>
        {m.axioms_used.length > 0 && (
          <div style={chipsRowStyle}>
            {m.axioms_used.slice(0, 6).map((a) => (
              <span key={a} style={chipStyle}>
                {a}
              </span>
            ))}
            {m.axioms_used.length > 6 && (
              <span style={chipMoreStyle}>+{m.axioms_used.length - 6} more</span>
            )}
          </div>
        )}
      </div>
      <div style={actionsStyle}>
        <a
          href={m.lean_url}
          target="_blank"
          rel="noreferrer"
          style={ghostBtn}
          title="Download the Lean 4 source"
        >
          Lean
        </a>
        <Link to="/theorem/$id" params={{ id: m.id }} style={primaryBtn}>
          View proof
        </Link>
      </div>
    </div>
  );
});

const containerStyle: React.CSSProperties = { display: 'grid', gap: 14 };
const headerStyle: React.CSSProperties = {
  display: 'flex',
  justifyContent: 'space-between',
  alignItems: 'baseline',
};
const headlineStyle: React.CSSProperties = { margin: 0, fontSize: 18 };
const metaStyle: React.CSSProperties = { fontSize: 12, color: 'var(--ink-500)' };
const resultGridStyle: React.CSSProperties = { display: 'grid', gap: 8 };
const resultLinkStyle: React.CSSProperties = { textDecoration: 'none', color: 'inherit' };
const resultMetaStyle: React.CSSProperties = {
  display: 'flex',
  gap: 12,
  alignItems: 'center',
  flexWrap: 'wrap',
};
const monoSmallStyle: React.CSSProperties = { fontFamily: 'var(--font-mono)', fontSize: 12 };
const domainSmallStyle: React.CSSProperties = {
  letterSpacing: '0.04em',
  textTransform: 'uppercase',
  fontWeight: 600,
  fontSize: 12,
};
const depthStyle: React.CSSProperties = { fontSize: 12 };
const chipsRowStyle: React.CSSProperties = { display: 'flex', gap: 6, flexWrap: 'wrap' };
const chipMoreStyle: React.CSSProperties = { fontSize: 11, color: 'var(--ink-500)' };
const actionsStyle: React.CSSProperties = { display: 'flex', gap: 8, alignItems: 'center' };

const cardStyle: React.CSSProperties = {
  display: 'grid',
  gridTemplateColumns: '1fr auto',
  gap: 14,
  alignItems: 'center',
  padding: 16,
  border: '1px solid var(--ink-200)',
  borderRadius: 10,
  background: 'var(--paper-0)',
};

const chipStyle: React.CSSProperties = {
  padding: '2px 8px',
  borderRadius: 4,
  border: '1px solid var(--ink-200)',
  fontFamily: 'var(--font-mono)',
  fontSize: 11,
  color: 'var(--ink-700)',
};

const ghostBtn: React.CSSProperties = {
  padding: '6px 12px',
  borderRadius: 6,
  border: '1px solid var(--ink-300)',
  color: 'var(--ink-700)',
  textDecoration: 'none',
  fontSize: 13,
  fontWeight: 600,
};

const primaryBtn: React.CSSProperties = {
  padding: '6px 12px',
  borderRadius: 6,
  background: 'var(--terracotta-700)',
  color: 'white',
  textDecoration: 'none',
  fontSize: 13,
  fontWeight: 600,
};
