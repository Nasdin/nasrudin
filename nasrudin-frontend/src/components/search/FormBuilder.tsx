import { useState } from 'react';
import type { SearchFilters } from '~/lib/types';

const DOMAINS = [
  'PureMath',
  'ClassicalMechanics',
  'Electromagnetism',
  'SpecialRelativity',
  'GeneralRelativity',
  'QuantumMechanics',
  'QuantumFieldTheory',
  'StatisticalMechanics',
  'Thermodynamics',
  'Optics',
  'FluidDynamics',
] as const;

const DIMENSION_PRESETS: { label: string; vec: number[] }[] = [
  { label: 'Energy', vec: [2, 1, -2, 0, 0, 0, 0] },
  { label: 'Momentum', vec: [1, 1, -1, 0, 0, 0, 0] },
  { label: 'Force', vec: [1, 1, -2, 0, 0, 0, 0] },
  { label: 'Action', vec: [2, 1, -1, 0, 0, 0, 0] },
  { label: 'Charge', vec: [0, 0, 1, 1, 0, 0, 0] },
  { label: 'Velocity', vec: [1, 0, -1, 0, 0, 0, 0] },
];

interface Props {
  filters: SearchFilters;
  setFilters: (f: SearchFilters) => void;
  onSubmit: () => void;
  busy: boolean;
}

/**
 * Filter-only mode: pick a domain, dimension preset, and required axioms;
 * server returns verified theorems matching the filter set without needing
 * a parsed conjecture. Powers the "show me everything derivable from
 * Lorentz invariance" use case.
 */
export function FormBuilder({ filters, setFilters, onSubmit, busy }: Props) {
  const [axiomDraft, setAxiomDraft] = useState('');

  const addAxiom = () => {
    const next = axiomDraft.trim();
    if (!next) return;
    if (filters.axioms_required.includes(next)) return;
    setFilters({ ...filters, axioms_required: [...filters.axioms_required, next] });
    setAxiomDraft('');
  };

  const removeAxiom = (a: string) => {
    setFilters({
      ...filters,
      axioms_required: filters.axioms_required.filter((x) => x !== a),
    });
  };

  const dimMatches = (preset: number[]) =>
    filters.dimension !== null &&
    filters.dimension.length === preset.length &&
    preset.every((v, i) => v === filters.dimension![i]);

  return (
    <div style={containerStyle}>
      <Field label="Domain">
        <select
          value={filters.domain ?? ''}
          onChange={(e) => setFilters({ ...filters, domain: e.target.value || null })}
          style={selectStyle}
        >
          <option value="">Any domain</option>
          {DOMAINS.map((d) => (
            <option key={d} value={d}>
              {d}
            </option>
          ))}
        </select>
      </Field>

      <Field label="Dimension">
        <div style={{ display: 'flex', flexWrap: 'wrap', gap: 6 }}>
          <button
            type="button"
            onClick={() => setFilters({ ...filters, dimension: null })}
            style={chipStyle(filters.dimension === null)}
          >
            Any
          </button>
          {DIMENSION_PRESETS.map((p) => (
            <button
              key={p.label}
              type="button"
              onClick={() => setFilters({ ...filters, dimension: p.vec })}
              style={chipStyle(dimMatches(p.vec))}
            >
              {p.label}
            </button>
          ))}
        </div>
      </Field>

      <Field label="Required axioms">
        <div style={{ display: 'flex', gap: 8, marginBottom: 6 }}>
          <input
            type="text"
            value={axiomDraft}
            onChange={(e) => setAxiomDraft(e.target.value)}
            onKeyDown={(e) => {
              if (e.key === 'Enter') {
                e.preventDefault();
                addAxiom();
              }
            }}
            placeholder="LorentzInvariance"
            style={textInputStyle}
          />
          <button type="button" onClick={addAxiom} style={addBtnStyle}>
            Add
          </button>
        </div>
        {filters.axioms_required.length > 0 && (
          <div style={{ display: 'flex', flexWrap: 'wrap', gap: 6 }}>
            {filters.axioms_required.map((a) => (
              <span key={a} style={tagStyle}>
                {a}{' '}
                <button
                  type="button"
                  onClick={() => removeAxiom(a)}
                  style={removeBtnStyle}
                  aria-label={`remove ${a}`}
                >
                  ×
                </button>
              </span>
            ))}
          </div>
        )}
      </Field>

      <Field label="Max depth">
        <input
          type="number"
          min={1}
          max={50}
          value={filters.max_depth ?? ''}
          onChange={(e) =>
            setFilters({
              ...filters,
              max_depth: e.target.value === '' ? null : Number.parseInt(e.target.value, 10),
            })
          }
          placeholder="any"
          style={{ ...textInputStyle, width: 120 }}
        />
      </Field>

      <div style={{ display: 'flex', justifyContent: 'flex-end' }}>
        <button type="button" onClick={onSubmit} disabled={busy} style={submitBtnStyle(busy)}>
          {busy ? 'Searching…' : 'Run filter'}
        </button>
      </div>
    </div>
  );
}

function Field({ label, children }: { label: string; children: React.ReactNode }) {
  return (
    <div style={{ display: 'grid', gap: 6 }}>
      <span style={{ fontSize: 11, letterSpacing: '0.04em', textTransform: 'uppercase', color: 'var(--ink-500)', fontWeight: 600 }}>
        {label}
      </span>
      {children}
    </div>
  );
}

const containerStyle: React.CSSProperties = {
  display: 'grid',
  gap: 14,
  padding: 16,
  border: '1px solid var(--ink-200)',
  borderRadius: 12,
  background: 'var(--paper-50)',
};

const selectStyle: React.CSSProperties = {
  padding: '8px 10px',
  borderRadius: 6,
  border: '1px solid var(--ink-200)',
  background: 'var(--paper-0)',
  fontSize: 14,
};

const textInputStyle: React.CSSProperties = {
  flex: 1,
  padding: '8px 10px',
  borderRadius: 6,
  border: '1px solid var(--ink-200)',
  background: 'var(--paper-0)',
  fontSize: 14,
  fontFamily: 'var(--font-mono)',
};

const addBtnStyle: React.CSSProperties = {
  padding: '8px 14px',
  borderRadius: 6,
  border: '1px solid var(--ink-300)',
  background: 'var(--paper-0)',
  cursor: 'pointer',
  fontSize: 13,
};

const tagStyle: React.CSSProperties = {
  display: 'inline-flex',
  alignItems: 'center',
  gap: 4,
  padding: '4px 10px',
  borderRadius: 999,
  background: 'var(--ink-900)',
  color: 'var(--paper-0)',
  fontSize: 12,
  fontFamily: 'var(--font-mono)',
};

const removeBtnStyle: React.CSSProperties = {
  background: 'transparent',
  border: 'none',
  color: 'var(--paper-0)',
  cursor: 'pointer',
  fontSize: 14,
  padding: 0,
  lineHeight: 1,
};

function chipStyle(active: boolean): React.CSSProperties {
  return {
    padding: '4px 10px',
    borderRadius: 6,
    border: '1px solid var(--ink-200)',
    background: active ? 'var(--ink-900)' : 'var(--paper-0)',
    color: active ? 'var(--paper-0)' : 'var(--ink-700)',
    fontSize: 12,
    cursor: 'pointer',
  };
}

function submitBtnStyle(busy: boolean): React.CSSProperties {
  return {
    padding: '8px 18px',
    borderRadius: 8,
    border: 'none',
    background: busy ? 'var(--ink-300)' : 'var(--terracotta-700)',
    color: 'white',
    fontWeight: 600,
    cursor: busy ? 'progress' : 'pointer',
  };
}
