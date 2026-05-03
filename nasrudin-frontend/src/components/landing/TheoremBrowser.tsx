import { Link } from '@tanstack/react-router';
import { memo, useState } from 'react';
import { VerificationBadge } from '~/components/theorem/VerificationBadge';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import { useRecentTheorems } from '~/lib/queries';

const FILTERS = [
  'All',
  'Quantum',
  'Relativity',
  'Classical mechanics',
  'Electromagnetism',
  'Pure math',
] as const;

const DOMAIN_LABEL: Record<string, string> = {
  PureMath: 'Pure math',
  ClassicalMechanics: 'Classical mechanics',
  Electromagnetism: 'Electromagnetism',
  SpecialRelativity: 'Relativity',
  GeneralRelativity: 'Relativity',
  QuantumMechanics: 'Quantum',
  QuantumFieldTheory: 'Quantum',
  StatisticalMechanics: 'Classical mechanics',
  Thermodynamics: 'Classical mechanics',
  Optics: 'Electromagnetism',
  FluidDynamics: 'Classical mechanics',
};

export const TheoremBrowser = memo(function TheoremBrowser() {
  const recent = useRecentTheorems(40);
  const [filter, setFilter] = useState<string>('All');
  const [expanded, setExpanded] = useState<string | null>(null);

  const all = recent.data?.theorems ?? [];
  const rows = filter === 'All' ? all : all.filter((t) => DOMAIN_LABEL[t.domain] === filter);

  return (
    <div className="browser">
      <div className="browser-head">
        <div className="browser-search">
          <svg
            width="14"
            height="14"
            viewBox="0 0 24 24"
            fill="none"
            stroke="currentColor"
            strokeWidth="1.8"
            strokeLinecap="round"
            strokeLinejoin="round"
            aria-hidden="true"
          >
            <circle cx="11" cy="11" r="7" />
            <path d="m21 21-4.3-4.3" />
          </svg>
          <span>theorem.statement contains …</span>
        </div>
        <div className="browser-filters">
          {FILTERS.map((f) => (
            <button
              type="button"
              key={f}
              className={`filter-chip ${filter === f ? 'active' : ''}`}
              onClick={() => {
                setExpanded(null);
                setFilter(f);
              }}
            >
              {f}
            </button>
          ))}
        </div>
      </div>
      <div className="browser-table">
        <div className="browser-row head">
          <span>ID</span>
          <span>Statement</span>
          <span>Name</span>
          <span>Domain</span>
          <span>Status</span>
          <span />
        </div>
        {rows.length === 0 && (
          <div style={{ padding: 32, textAlign: 'center', color: 'var(--ink-500)' }}>
            {recent.isPending ? 'Loading…' : 'No verified theorems yet — start a worker.'}
          </div>
        )}
        {rows.slice(0, 8).map((t) => {
          const id = bytesToHex(t.id);
          const stmt = t.latex ?? t.canonical_statement;
          const isOpen = expanded === id;
          return (
            <BrowserRow
              key={id}
              id={id}
              stmt={stmt}
              t={t}
              isOpen={isOpen}
              setExpanded={setExpanded}
            />
          );
        })}
      </div>
      {rows.length > 0 && (
        <div
          style={{
            padding: '14px 24px',
            borderTop: '1px solid var(--paper-200)',
            background: 'var(--paper-50)',
            textAlign: 'center',
            fontSize: 13,
          }}
        >
          <Link
            to="/browse"
            style={{
              color: 'var(--terracotta-700)',
              textDecorationColor: 'var(--terracotta-100)',
              fontWeight: 500,
            }}
          >
            View the full corpus →
          </Link>
        </div>
      )}
    </div>
  );
});

function BrowserRow({
  id,
  stmt,
  t,
  isOpen,
  setExpanded,
}: {
  id: string;
  stmt: string;
  t: import('~/lib/types').Theorem;
  isOpen: boolean;
  setExpanded: (v: string | null) => void;
}) {
  return (
    <>
      <button
        type="button"
        className={`browser-row ${isOpen ? 'expanded' : ''}`}
        onClick={() => setExpanded(isOpen ? null : id)}
        style={{
          background: 'transparent',
          border: 'none',
          textAlign: 'left',
          width: '100%',
          font: 'inherit',
        }}
      >
        <span className="browser-id">{id.slice(0, 8)}</span>
        <span className="browser-stmt">
          <MathExpr source={stmt} />
        </span>
        <span className="browser-name">
          {t.verification_tactic ?? `gen ${t.generation ?? '—'}`}
        </span>
        <span className="browser-dom">{DOMAIN_LABEL[t.domain] ?? t.domain}</span>
        <span className="browser-status">
          <VerificationBadge
            status={t.status}
            tactic={t.verification_tactic}
            submitterTrusted={t.worker_trusted}
            rejectedReason={t.rejected_reason}
            compact
          />
        </span>
        <span className="browser-chev">
          <svg
            width="14"
            height="14"
            viewBox="0 0 24 24"
            fill="none"
            stroke="currentColor"
            strokeWidth="2"
            strokeLinecap="round"
            strokeLinejoin="round"
            aria-hidden="true"
          >
            <polyline points="6 9 12 15 18 9" />
          </svg>
        </span>
      </button>
      {isOpen && (
        <div className="browser-detail">
          <div className="browser-detail-block">
            <h5>Statement</h5>
            <div className="full-stmt">
              <MathExpr source={stmt} block />
            </div>
            <div className="meta-row">
              <div>
                generation <strong>{t.generation ?? '—'}</strong>
              </div>
              <div>
                tactic <strong>{t.verification_tactic ?? '—'}</strong>
              </div>
              <div>
                depth <strong>{t.depth ?? '—'}</strong>
              </div>
              <div>
                domain <strong>{t.domain}</strong>
              </div>
            </div>
          </div>
          <div className="browser-detail-block">
            <h5>Lean 4 proof</h5>
            <pre className="browser-proof">{t.lean_source}</pre>
          </div>
          <div className="browser-detail-actions">
            <Link
              to="/theorem/$id"
              params={{ id }}
              className="btn btn-secondary"
              onClick={(e) => e.stopPropagation()}
            >
              Open theorem page
            </Link>
            <span className="btn btn-ghost" style={{ cursor: 'default' }}>
              Re-verify locally with{' '}
              <code
                style={{
                  fontFamily: 'var(--font-mono)',
                  fontSize: 12,
                  marginLeft: 6,
                  color: 'var(--ink-900)',
                }}
              >
                lake build
              </code>
            </span>
          </div>
        </div>
      )}
    </>
  );
}

