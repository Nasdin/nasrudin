import { createFileRoute, Link, redirect } from '@tanstack/react-router';
import { useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import { useMe, useMeStats, useSavedSearches } from '~/lib/queries';

export const Route = createFileRoute('/library')({ component: LibraryPage });

type Tab = 'theorems' | 'searches';

function LibraryPage() {
  const me = useMe();
  const stats = useMeStats();
  const saved = useSavedSearches();
  const [tab, setTab] = useState<Tab>('theorems');

  if (me.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });

  const recentTheorems = stats.data?.theorems_recent ?? [];
  const savedSearches = saved.data?.saved_searches ?? [];

  return (
    <div className="app">
      <AppHeader active="library" />
      <div className="container-wide">
        <div className="page-head">
          <span className="overline">Your library</span>
          <h1>
            My library —{' '}
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              every theorem you've touched.
            </em>
          </h1>
          <p className="lede">
            Theorems your workers verified live here alongside the searches you've saved. Click any
            row to open its full Lean 4 proof.
          </p>
        </div>

        <div className="page-body">
          <div className="lead-tabs" style={{ margin: '0 0 24px' }}>
            <button
              type="button"
              className={`lead-tab ${tab === 'theorems' ? 'active' : ''}`}
              onClick={() => setTab('theorems')}
            >
              Theorems · {recentTheorems.length}
            </button>
            <button
              type="button"
              className={`lead-tab ${tab === 'searches' ? 'active' : ''}`}
              onClick={() => setTab('searches')}
            >
              Saved searches · {savedSearches.length}
            </button>
          </div>

          {tab === 'theorems' &&
            (recentTheorems.length === 0 ? (
              <EmptyState>
                Once a worker you own verifies a theorem, it'll appear here. Run a worker via{' '}
                <Link to="/api-keys">a worker API key →</Link>
              </EmptyState>
            ) : (
              <ul className="saved-list">
                {recentTheorems.map((t) => {
                  const id = bytesToHex(t.id);
                  return (
                    <li key={id}>
                      <Link
                        to="/theorem/$id"
                        params={{ id }}
                        style={{
                          textDecoration: 'none',
                          color: 'inherit',
                          display: 'contents',
                        }}
                      >
                        <span className="saved-stmt">
                          <MathExpr source={t.latex ?? t.canonical_statement} />
                        </span>
                        <span className="saved-domain">{t.domain}</span>
                        <span className="saved-date">
                          {new Date(t.created_at).toLocaleDateString()}
                        </span>
                      </Link>
                    </li>
                  );
                })}
              </ul>
            ))}

          {tab === 'searches' &&
            (savedSearches.length === 0 ? (
              <EmptyState>
                You haven't saved any searches yet. Save a query from{' '}
                <Link to="/browse">the corpus →</Link>
              </EmptyState>
            ) : (
              <ul className="saved-list">
                {savedSearches.map((s) => (
                  <li key={s.id}>
                    <span className="saved-stmt">{s.label ?? s.latex}</span>
                    <span className="saved-domain">search</span>
                    <span className="saved-date">
                      {new Date(s.created_at).toLocaleDateString()}
                    </span>
                  </li>
                ))}
              </ul>
            ))}
        </div>
      </div>
      <AppFooter />
    </div>
  );
}

function EmptyState({ children }: { children: React.ReactNode }) {
  return (
    <div
      style={{
        padding: '64px 32px',
        textAlign: 'center',
        color: 'var(--ink-500)',
        fontSize: 15,
        border: '1px dashed var(--paper-300)',
        borderRadius: 'var(--radius-lg)',
        background: 'var(--paper-50)',
      }}
    >
      {children}
    </div>
  );
}
