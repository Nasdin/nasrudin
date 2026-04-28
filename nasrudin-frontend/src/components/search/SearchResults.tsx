import { Link } from '@tanstack/react-router';
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
    <div style={{ display: 'grid', gap: 14 }}>
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'baseline' }}>
        <h2 style={{ margin: 0, fontSize: 18 }}>{TIER_HEADLINE[tier]}</h2>
        <span style={{ fontSize: 12, color: 'var(--ink-500)' }}>
          {matches.length} result{matches.length === 1 ? '' : 's'} · {tookMs} ms
        </span>
      </div>
      {matches.map((m) => (
        <Result key={m.id} m={m} />
      ))}
    </div>
  );
}

function Result({ m }: { m: SearchMatchItem }) {
  const stmt = m.statement_latex ?? m.canonical_statement;
  return (
    <div className="result-card" style={cardStyle}>
      <div style={{ display: 'grid', gap: 8 }}>
        <Link
          to="/theorem/$id"
          params={{ id: m.id }}
          style={{ textDecoration: 'none', color: 'inherit' }}
        >
          <div className="result-stmt">
            <MathExpr source={stmt} />
          </div>
        </Link>
        <div className="result-meta" style={{ display: 'flex', gap: 12, alignItems: 'center', flexWrap: 'wrap' }}>
          <MatchBadge kind={m.match} />
          <span style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>
            thm:{m.id.slice(0, 8)}
          </span>
          <span className="dot">·</span>
          <span style={{ letterSpacing: '0.04em', textTransform: 'uppercase', fontWeight: 600, fontSize: 12 }}>
            {m.domain}
          </span>
          <span className="dot">·</span>
          <span style={{ fontSize: 12 }}>depth {m.depth ?? 0}</span>
        </div>
        {m.axioms_used.length > 0 && (
          <div style={{ display: 'flex', gap: 6, flexWrap: 'wrap' }}>
            {m.axioms_used.slice(0, 6).map((a) => (
              <span key={a} style={chipStyle}>
                {a}
              </span>
            ))}
            {m.axioms_used.length > 6 && (
              <span style={{ fontSize: 11, color: 'var(--ink-500)' }}>
                +{m.axioms_used.length - 6} more
              </span>
            )}
          </div>
        )}
      </div>
      <div style={{ display: 'flex', gap: 8, alignItems: 'center' }}>
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
}

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
