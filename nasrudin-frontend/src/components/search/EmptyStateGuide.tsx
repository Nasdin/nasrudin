import type { SearchInputFormat } from '~/lib/types';

const EXAMPLES: { label: string; mode: Exclude<SearchInputFormat, 'form'>; input: string }[] = [
  { label: 'Mass-energy equivalence', mode: 'latex', input: 'E = mc^2' },
  { label: 'Canonical commutation', mode: 'latex', input: '[x, p] = i \\hbar' },
  { label: 'Energy-momentum relation', mode: 'latex', input: 'E^2 = (pc)^2 + (mc^2)^2' },
  { label: 'Maxwell — no monopoles', mode: 'math', input: 'div(B) = 0' },
];

interface Props {
  onPick: (mode: Exclude<SearchInputFormat, 'form'>, input: string) => void;
}

/**
 * Empty / first-load state. Click an example to populate the search box and
 * fire it. Shows what the system is built to do without making the user guess.
 */
export function EmptyStateGuide({ onPick }: Props) {
  return (
    <div style={containerStyle}>
      <div>
        <h2 style={{ margin: '0 0 8px 0', fontSize: 18 }}>Try one of these</h2>
        <p style={{ margin: 0, color: 'var(--ink-500)', fontSize: 14 }}>
          A click below will run the search. The system parses your conjecture, AC-canonicalizes
          it, and looks up an exact verified theorem before falling back to structural unification
          and near-miss ranking.
        </p>
      </div>
      <div style={{ display: 'grid', gap: 10 }}>
        {EXAMPLES.map((ex) => (
          <button
            key={ex.input}
            type="button"
            onClick={() => onPick(ex.mode, ex.input)}
            style={cardStyle}
          >
            <div style={{ fontFamily: 'var(--font-mono)', fontSize: 14 }}>{ex.input}</div>
            <div style={{ fontSize: 12, color: 'var(--ink-500)' }}>
              {ex.label} · {ex.mode}
            </div>
          </button>
        ))}
      </div>
    </div>
  );
}

const containerStyle: React.CSSProperties = {
  display: 'grid',
  gap: 16,
  padding: 18,
  border: '1px dashed var(--ink-300)',
  borderRadius: 12,
  background: 'var(--paper-50)',
};

const cardStyle: React.CSSProperties = {
  display: 'grid',
  gap: 4,
  padding: 12,
  border: '1px solid var(--ink-200)',
  borderRadius: 8,
  background: 'var(--paper-0)',
  textAlign: 'left',
  cursor: 'pointer',
  color: 'var(--ink-900)',
};
