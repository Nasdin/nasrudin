import { Component, useEffect, type CSSProperties, type ReactNode } from 'react';
import { Math as MathExpr } from '~/lib/katex';
import type { SearchInputFormat } from '~/lib/types';

const MODES: { id: Exclude<SearchInputFormat, 'form'>; label: string; placeholder: string }[] = [
  {
    id: 'latex',
    label: 'LaTeX',
    placeholder: '[x, p] = i \\hbar',
  },
  {
    id: 'math',
    label: 'Math',
    placeholder: '[x, p] = i * hbar',
  },
  {
    id: 'sexpr',
    label: 'S-expr',
    placeholder: '(= (- (* v:x v:p) (* v:p v:x)) (* v:i c:ReducedPlanck))',
  },
];

interface Props {
  mode: Exclude<SearchInputFormat, 'form'>;
  setMode: (m: Exclude<SearchInputFormat, 'form'>) => void;
  value: string;
  setValue: (v: string) => void;
  onSubmit: () => void;
  busy: boolean;
}

/** Tabbed expression input with live KaTeX preview (LaTeX mode only). */
export function SearchBox({ mode, setMode, value, setValue, onSubmit, busy }: Props) {
  // ⌘↵ / Ctrl+↵ submit shortcut, scoped to the document.
  useEffect(() => {
    function handler(e: KeyboardEvent) {
      if ((e.metaKey || e.ctrlKey) && e.key === 'Enter') {
        e.preventDefault();
        if (!busy) onSubmit();
      }
    }
    window.addEventListener('keydown', handler);
    return () => window.removeEventListener('keydown', handler);
  }, [onSubmit, busy]);

  const placeholder = MODES.find((m) => m.id === mode)?.placeholder ?? '';

  return (
    <div className="search-box" style={containerStyle}>
      <div style={{ display: 'flex', gap: 4, marginBottom: 8 }}>
        {MODES.map((m) => (
          <button
            key={m.id}
            type="button"
            onClick={() => setMode(m.id)}
            style={tabStyle(mode === m.id)}
            aria-pressed={mode === m.id}
          >
            {m.label}
          </button>
        ))}
      </div>
      <textarea
        value={value}
        onChange={(e) => setValue(e.target.value)}
        placeholder={placeholder}
        rows={3}
        spellCheck={false}
        style={textareaStyle}
      />
      {mode === 'latex' && value.trim().length > 0 && (
        <div style={previewStyle}>
          <span style={{ fontSize: 11, color: 'var(--ink-500)', letterSpacing: '0.04em' }}>
            PREVIEW
          </span>
          <PreviewBoundary fallback={<em style={{ color: 'var(--ink-500)' }}>preview unavailable</em>}>
            <MathExpr source={value} block={false} />
          </PreviewBoundary>
        </div>
      )}
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
        <span style={{ fontSize: 12, color: 'var(--ink-500)' }}>⌘↵ to search</span>
        <button type="button" onClick={onSubmit} disabled={busy || !value.trim()} style={submitStyle(busy)}>
          {busy ? 'Searching…' : 'Search the corpus'}
        </button>
      </div>
    </div>
  );
}

interface BoundaryProps {
  children: ReactNode;
  fallback: ReactNode;
}

interface BoundaryState {
  hasError: boolean;
}

class PreviewBoundary extends Component<BoundaryProps, BoundaryState> {
  constructor(props: BoundaryProps) {
    super(props);
    this.state = { hasError: false };
  }
  static getDerivedStateFromError(): BoundaryState {
    return { hasError: true };
  }
  override componentDidUpdate(prev: BoundaryProps) {
    if (prev.children !== this.props.children && this.state.hasError) {
      this.setState({ hasError: false });
    }
  }
  override render() {
    return this.state.hasError ? this.props.fallback : this.props.children;
  }
}

const containerStyle: CSSProperties = {
  border: '1px solid var(--ink-200)',
  borderRadius: 12,
  padding: 16,
  background: 'var(--paper-50)',
  display: 'grid',
  gap: 10,
};

const textareaStyle: CSSProperties = {
  width: '100%',
  border: '1px solid var(--ink-200)',
  borderRadius: 8,
  padding: '12px 14px',
  fontFamily: 'var(--font-mono)',
  fontSize: 15,
  resize: 'vertical',
  background: 'var(--paper-0)',
  color: 'var(--ink-900)',
};

const previewStyle: CSSProperties = {
  border: '1px dashed var(--ink-200)',
  borderRadius: 8,
  padding: '10px 14px',
  background: 'var(--paper-0)',
  display: 'grid',
  gap: 4,
};

function tabStyle(active: boolean): CSSProperties {
  return {
    padding: '6px 14px',
    borderRadius: 6,
    border: '1px solid var(--ink-200)',
    background: active ? 'var(--ink-900)' : 'var(--paper-0)',
    color: active ? 'var(--paper-0)' : 'var(--ink-700)',
    fontSize: 13,
    fontWeight: 600,
    cursor: 'pointer',
  };
}

function submitStyle(busy: boolean): CSSProperties {
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
