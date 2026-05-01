import { memo } from 'react';
import type { LlmSuggestion } from '~/lib/types';

const headRowStyle: React.CSSProperties = {
  display: 'flex',
  justifyContent: 'space-between',
  alignItems: 'baseline',
};
const chosenStyle: React.CSSProperties = { color: 'var(--terracotta-700)' };
const targetStyle: React.CSSProperties = {
  fontFamily: 'var(--font-mono)',
  marginTop: 8,
  fontSize: 14,
  color: 'var(--ink-700)',
};
const rationaleStyle: React.CSSProperties = {
  marginTop: 8,
  color: 'var(--ink-700)',
  fontSize: 14,
};
const detailsStyle: React.CSSProperties = { marginTop: 8 };
const summaryStyle: React.CSSProperties = {
  cursor: 'pointer',
  fontSize: 13,
  color: 'var(--ink-500)',
};
const axiomListStyle: React.CSSProperties = {
  marginTop: 8,
  fontFamily: 'var(--font-mono)',
  fontSize: 13,
  paddingLeft: 16,
};
const seedListStyle: React.CSSProperties = {
  fontFamily: 'var(--font-mono)',
  fontSize: 13,
  paddingLeft: 16,
};
const seedHeadStyle: React.CSSProperties = {
  fontSize: 13,
  marginTop: 8,
  color: 'var(--ink-500)',
};

const cardSelected: React.CSSProperties = {
  border: '2px solid var(--terracotta-700)',
  borderRadius: 8,
  padding: 16,
  marginBottom: 12,
  cursor: 'pointer',
  background: 'var(--paper-50)',
};
const cardUnselected: React.CSSProperties = {
  border: '1px solid var(--paper-200)',
  borderRadius: 8,
  padding: 16,
  marginBottom: 12,
  cursor: 'pointer',
  background: 'var(--bg-raised)',
};

export const SuggestionCard = memo(function SuggestionCard({
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
    <div style={selected ? cardSelected : cardUnselected} onClick={onSelect}>
      <div style={headRowStyle}>
        <strong>Suggestion #{index + 1}</strong>
        {selected && <span style={chosenStyle}>✓ chosen</span>}
      </div>
      {suggestion.target_shape && (
        <div style={targetStyle}>target: {suggestion.target_shape}</div>
      )}
      <div style={rationaleStyle}>{suggestion.rationale}</div>
      <details style={detailsStyle}>
        <summary style={summaryStyle}>
          axioms ({suggestion.axiom_set.length}) · seeds ({suggestion.initial_population.length})
        </summary>
        <ul style={axiomListStyle}>
          {suggestion.axiom_set.map((a) => (
            <li key={a}>{a}</li>
          ))}
        </ul>
        <div style={seedHeadStyle}>Initial population:</div>
        <ul style={seedListStyle}>
          {suggestion.initial_population.map((s, i) => (
            <li key={i}>{s}</li>
          ))}
        </ul>
      </details>
    </div>
  );
});
