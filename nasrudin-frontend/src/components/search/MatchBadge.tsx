import type { SearchMatchKind } from '~/lib/types';

/** Small pill that explains how a result was matched (exact / unify / near-miss). */
export function MatchBadge({ kind }: { kind: SearchMatchKind }) {
  switch (kind.kind) {
    case 'exact':
      return (
        <span
          title="AC-canonical hash matched exactly. Your conjecture is in the corpus, with a verified Lean proof."
          style={badgeStyle('var(--terracotta-700)')}
        >
          ✓ Exact match
        </span>
      );
    case 'unify': {
      const bindingsCount = Object.keys(kind.bindings).length;
      const summary = bindingsCount === 0
        ? 'Filter match'
        : `Pattern unified · ${bindingsCount} binding${bindingsCount === 1 ? '' : 's'}`;
      return (
        <span
          title={
            bindingsCount === 0
              ? 'Returned by structured filter without unification.'
              : Object.entries(kind.bindings)
                  .map(([k, v]) => `${k} ↦ ${v}`)
                  .join('   ')
          }
          style={badgeStyle('var(--ink-700)')}
        >
          ↔ {summary}
        </span>
      );
    }
    case 'near_miss': {
      const pct = Math.round((1 - kind.score) * 100);
      return (
        <span
          title={`Token Levenshtein ${kind.token_distance} · dim Hamming ${kind.dim_hamming} · axiom Jaccard ${kind.axiom_jaccard.toFixed(2)}`}
          style={badgeStyle('var(--ink-500)')}
        >
          ≈ {pct}% similar
        </span>
      );
    }
  }
}

function badgeStyle(color: string): React.CSSProperties {
  return {
    display: 'inline-block',
    padding: '2px 8px',
    borderRadius: 999,
    border: `1px solid ${color}`,
    color,
    fontSize: 11,
    letterSpacing: '0.04em',
    textTransform: 'uppercase',
    fontWeight: 600,
  };
}
