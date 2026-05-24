import { createFileRoute } from '@tanstack/react-router';
import { useState } from 'react';
import { EmptyStateGuide } from '~/components/search/EmptyStateGuide';
import { FormBuilder } from '~/components/search/FormBuilder';
import { SearchBox } from '~/components/search/SearchBox';
import { SearchResults } from '~/components/search/SearchResults';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useSearch } from '~/lib/queries';
import type { SearchFilters, SearchInputFormat, SearchRequest } from '~/lib/types';

export const Route = createFileRoute('/search/')({ component: SearchPage });

const EMPTY_FILTERS: SearchFilters = {
  domain: null,
  dimension: null,
  axioms_required: [],
  max_depth: null,
};

function SearchPage() {
  const [mode, setMode] = useState<Exclude<SearchInputFormat, 'form'>>('latex');
  const [input, setInput] = useState('');
  const [filters, setFilters] = useState<SearchFilters>(EMPTY_FILTERS);
  const [showForm, setShowForm] = useState(false);
  const search = useSearch();

  const submit = (req?: Partial<SearchRequest>) => {
    const finalReq: SearchRequest = {
      input: req?.input ?? input,
      input_format: req?.input_format ?? mode,
      filters: req?.filters ?? filters,
      limit: 20,
    };
    search.mutate(finalReq);
  };

  const submitForm = () => {
    search.mutate({
      input: '',
      input_format: 'form',
      filters,
      limit: 20,
    });
  };

  const fillExample = (m: Exclude<SearchInputFormat, 'form'>, v: string) => {
    setMode(m);
    setInput(v);
    submit({ input: v, input_format: m });
  };

  const result = search.data;

  return (
    <div className="app">
      <AppHeader />
      <div className="container-wide" style={{ paddingTop: 24, paddingBottom: 48 }}>
        <div className="page-head" style={{ paddingBottom: 16, borderBottom: 'none' }}>
          <span className="overline">Discover</span>
          <h1>
            <em style={{ fontStyle: 'italic', color: 'var(--terracotta-700)', fontWeight: 300 }}>
              Type a conjecture.
            </em>{' '}
            Find a verified proof.
          </h1>
          <p className="lede">
            The corpus contains machine-generated theorems, each verified by Lean&nbsp;4 against
            PhysLean axioms. If your conjecture is in there, you'll get the proof, the axiom set,
            and the Lean source — ready to cite.
          </p>
        </div>

        <div className="search-shell">
          <div style={{ display: 'grid', gap: 18 }}>
            <SearchBox
              mode={mode}
              setMode={setMode}
              value={input}
              setValue={setInput}
              onSubmit={() => submit()}
              busy={search.isPending}
            />

            <button
              type="button"
              onClick={() => setShowForm((s) => !s)}
              style={{
                background: 'transparent',
                border: 'none',
                color: 'var(--terracotta-700)',
                cursor: 'pointer',
                padding: 0,
                fontSize: 13,
                textAlign: 'left',
              }}
            >
              {showForm ? '× Hide structured filters' : '+ Or browse by axiom set / dimension (no conjecture needed)'}
            </button>

            {showForm && (
              <FormBuilder
                filters={filters}
                setFilters={setFilters}
                onSubmit={submitForm}
                busy={search.isPending}
              />
            )}

            {search.isError && (
              <div style={errorBox}>
                {(search.error as Error)?.message ?? 'Something went wrong.'}
              </div>
            )}

            {result?.parse_error && (
              <div style={errorBox}>
                <strong>Parse error.</strong>{' '}
                <span style={{ fontFamily: 'var(--font-mono)' }}>{result.parse_error}</span>
                <div style={{ marginTop: 4, fontSize: 12, color: 'var(--ink-500)' }}>
                  Try switching modes or check the syntax.
                </div>
              </div>
            )}

            {result && !result.parse_error && result.tier !== 'empty' && (
              <SearchResults tier={result.tier} matches={result.matches} tookMs={result.took_ms} />
            )}

            {result && !result.parse_error && result.tier === 'empty' && (
              <div style={emptyBox}>
                <strong>No matches.</strong> The corpus has no theorems unifying with this conjecture
                under the chosen filters. Try loosening the dimension or required-axiom set, or use the
                structured filter mode to see what's nearby.
              </div>
            )}

            {!result && !search.isPending && <EmptyStateGuide onPick={fillExample} />}
          </div>

          <aside className="search-aside">
            <SidebarBlurb />
          </aside>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}

function SidebarBlurb() {
  return (
    <div className="search-aside-blurb">
      <h3 style={{ marginTop: 0, fontSize: 14, letterSpacing: '0.04em', textTransform: 'uppercase' }}>
        How matching works
      </h3>
      <ol style={{ paddingLeft: 18, fontSize: 13, color: 'var(--ink-700)', margin: 0 }}>
        <li style={{ marginBottom: 8 }}>
          <strong>Exact</strong> — Your conjecture is canonicalized (commutativity, associativity, Eq
          symmetry) and looked up by hash. If a verified theorem matches, you're done.
        </li>
        <li style={{ marginBottom: 8 }}>
          <strong>Unify</strong> — Free variables in your conjecture are treated as pattern holes; any
          theorem whose statement matches structurally is returned with the bindings shown.
        </li>
        <li>
          <strong>Near-miss</strong> — When no unification, the closest theorems are ranked by token
          edit distance, dimensional Hamming distance, and axiom-set Jaccard.
        </li>
      </ol>
    </div>
  );
}

const errorBox: React.CSSProperties = {
  border: '1px solid var(--terracotta-700)',
  borderRadius: 8,
  padding: '10px 14px',
  color: 'var(--terracotta-700)',
  background: 'var(--paper-0)',
};

const emptyBox: React.CSSProperties = {
  border: '1px dashed var(--ink-300)',
  borderRadius: 8,
  padding: '14px 16px',
  color: 'var(--ink-700)',
  background: 'var(--paper-50)',
};

