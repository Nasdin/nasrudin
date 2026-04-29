import type { LlmSuggestion } from '~/lib/types';

export function SuggestionCard({
  suggestion,
  index,
  selected,
  onSelect,
}: {
  suggestion: LlmSuggestion;
  index: number;
  selected: boolean;
  onSelect: () => void;
}) {
  return (
    <div
      style={{
        border: selected
          ? '2px solid var(--terracotta-700)'
          : '1px solid var(--paper-200)',
        borderRadius: 8,
        padding: 16,
        marginBottom: 12,
        cursor: 'pointer',
        background: selected ? 'var(--paper-50)' : 'var(--bg-raised)',
      }}
      onClick={onSelect}
    >
      <div
        style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'baseline',
        }}
      >
        <strong>Suggestion #{index + 1}</strong>
        {selected && <span style={{ color: 'var(--terracotta-700)' }}>✓ chosen</span>}
      </div>
      {suggestion.target_shape && (
        <div
          style={{
            fontFamily: 'var(--font-mono)',
            marginTop: 8,
            fontSize: 14,
            color: 'var(--ink-700)',
          }}
        >
          target: {suggestion.target_shape}
        </div>
      )}
      <div style={{ marginTop: 8, color: 'var(--ink-700)', fontSize: 14 }}>
        {suggestion.rationale}
      </div>
      <details style={{ marginTop: 8 }}>
        <summary
          style={{
            cursor: 'pointer',
            fontSize: 13,
            color: 'var(--ink-500)',
          }}
        >
          axioms ({suggestion.axiom_set.length}) · seeds ({suggestion.initial_population.length})
        </summary>
        <ul
          style={{
            marginTop: 8,
            fontFamily: 'var(--font-mono)',
            fontSize: 13,
            paddingLeft: 16,
          }}
        >
          {suggestion.axiom_set.map((a) => (
            <li key={a}>{a}</li>
          ))}
        </ul>
        <div style={{ fontSize: 13, marginTop: 8, color: 'var(--ink-500)' }}>
          Initial population:
        </div>
        <ul
          style={{
            fontFamily: 'var(--font-mono)',
            fontSize: 13,
            paddingLeft: 16,
          }}
        >
          {suggestion.initial_population.map((s, i) => (
            <li key={i}>{s}</li>
          ))}
        </ul>
      </details>
    </div>
  );
}
