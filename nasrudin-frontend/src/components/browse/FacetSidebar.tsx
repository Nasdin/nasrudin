import type { Domain } from '~/lib/types';

export const DOMAIN_LABELS: Array<{ value: Domain | null; label: string }> = [
  { value: null, label: 'All' },
  { value: 'PureMath', label: 'Pure math' },
  { value: 'ClassicalMechanics', label: 'Classical mechanics' },
  { value: 'Electromagnetism', label: 'Electromagnetism' },
  { value: 'SpecialRelativity', label: 'Special relativity' },
  { value: 'GeneralRelativity', label: 'General relativity' },
  { value: 'QuantumMechanics', label: 'Quantum mechanics' },
  { value: 'Thermodynamics', label: 'Thermodynamics' },
];

export function FacetSidebar({
  counts,
  active,
  onChange,
}: {
  counts: Record<string, number>;
  active: Domain | null;
  onChange: (d: Domain | null) => void;
}) {
  return (
    <aside>
      <div className="facet-group">
        <h5>Domain</h5>
        <ul className="facet-list">
          {DOMAIN_LABELS.map((d) => (
            <li
              key={d.label}
              className={active === d.value ? 'active' : ''}
              onClick={() => onChange(d.value)}
              onKeyDown={(e) => {
                if (e.key === 'Enter' || e.key === ' ') onChange(d.value);
              }}
              // biome-ignore lint/a11y/noNoninteractiveTabindex: facet rows are <li> in a <ul> for semantic grouping but act as click targets; tabindex makes them keyboard-focusable so the onKeyDown handler can fire.
              tabIndex={0}
              style={{ cursor: 'pointer' }}
            >
              <span>{d.label}</span>
              <span className="count">{(counts[d.value ?? ''] ?? 0).toLocaleString()}</span>
            </li>
          ))}
        </ul>
      </div>
    </aside>
  );
}
