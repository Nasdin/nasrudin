import { createFileRoute, Link } from '@tanstack/react-router';
import { useDebouncedValue } from '@tanstack/react-pacer';
import { type FormEvent, useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { Math } from '~/lib/katex';
import { useConceptSearch } from '~/lib/queries';
import type { ConceptHit } from '~/lib/types';

export const Route = createFileRoute('/search/concept')({ component: ConceptSearchPage });

function ConceptSearchPage() {
  const [draft, setDraft] = useState('');
  // @tanstack/react-pacer v0.22+ returns `[debouncedValue, debouncerInstance]`.
  // We only need the value; the instance lets you `flush()` etc. but we don't.
  const [debouncedDraft] = useDebouncedValue(draft, { wait: 300 });
  const [includePending, setIncludePending] = useState(true);
  const search = useConceptSearch(debouncedDraft.trim(), { includePending });

  const onSubmit = (e: FormEvent) => {
    e.preventDefault();
    // Form submit is now just for UX - the query already runs via debounced value
  };

  return (
    <div className="app">
      <AppHeader active="search" />
      <div className="container-wide" style={{ maxWidth: 1080 }}>
        <div className="page-head">
          <span className="overline">Concept search</span>
          <h1>
            Find theorems &amp; conjectures —{' '}
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              describe what you're looking for in plain English.
            </em>
          </h1>
          <p className="lede">
            Try "energy and mass", "photon momentum", "kinetic energy in classical
            mechanics". Hits include both <strong>verified theorems</strong> and{' '}
            <strong>conjectures-in-flight</strong> matching your phrase.
          </p>
        </div>

        <form onSubmit={onSubmit} className="concept-search-bar">
          <input
            type="text"
            value={draft}
            onChange={(e) => setDraft(e.target.value)}
            placeholder="all the equations that have to do with Energy"
            className="concept-search-input"
          />
          <label className="concept-search-toggle">
            <input
              type="checkbox"
              checked={includePending}
              onChange={(e) => setIncludePending(e.target.checked)}
            />
            include conjectures
          </label>
          <button
            type="submit"
            className="btn btn-primary concept-search-submit"
            disabled={draft.trim().length === 0}
          >
            Search
          </button>
        </form>

        {search.data && !search.data.embed_available && (
          <div
            style={{
              padding: 12,
              marginBottom: 16,
              border: '1px solid var(--paper-200)',
              borderRadius: 'var(--radius-md)',
              color: 'var(--ink-500)',
              fontSize: 13,
            }}
          >
            Embedding index isn't loaded — semantic search is disabled, results are
            substring-only. Set <code>NASRUDIN_EMBED_ENABLED=1</code> on the API and
            rebuild the index to get semantic recall.
          </div>
        )}

        {search.isPending && debouncedDraft.trim() && (
          <div style={{ color: 'var(--ink-500)' }}>Searching…</div>
        )}

        {search.data && (
          <div style={{ marginBottom: 12, color: 'var(--ink-500)', fontSize: 13 }}>
            {search.data.hits.length} hit{search.data.hits.length === 1 ? '' : 's'} ·{' '}
            {search.data.took_ms} ms
          </div>
        )}

        {search.data && search.data.hits.length === 0 && debouncedDraft.trim() && (
          <div className="card">
            No matches for <em>"{debouncedDraft.trim()}"</em>. Try a broader phrase, or toggle
            "include conjectures" if you only see verified rows.
          </div>
        )}

        {search.data?.hits.map((h) => <ConceptHitCard key={h.theorem_id} hit={h} />)}
      </div>
      <AppFooter />
    </div>
  );
}

function ConceptHitCard({ hit }: { hit: ConceptHit }) {
  return (
    <Link
      to="/theorem/$id"
      params={{ id: hit.theorem_id }}
      style={{
        display: 'block',
        padding: 16,
        marginBottom: 10,
        border: '1px solid var(--paper-200)',
        borderRadius: 'var(--radius-md)',
        background: 'var(--bg-raised)',
        textDecoration: 'none',
        color: 'inherit',
      }}
    >
      <div
        style={{
          display: 'flex',
          alignItems: 'baseline',
          gap: 12,
          marginBottom: 8,
          fontSize: 12,
          fontFamily: 'var(--font-mono)',
          color: 'var(--ink-500)',
        }}
      >
        <StatusPill status={hit.status} />
        <span>{hit.domain}</span>
        {hit.depth != null && <span>depth {hit.depth}</span>}
        <span style={{ marginLeft: 'auto' }}>
          score {hit.score.toFixed(2)} · {hit.source}
        </span>
      </div>
      {hit.latex ? (
        <>
          <div style={{ fontSize: 18 }}>
            <Math source={hit.latex} block />
          </div>
          <div
            style={{
              marginTop: 6,
              fontFamily: 'var(--font-mono)',
              fontSize: 12,
              color: 'var(--ink-500)',
            }}
          >
            {hit.canonical_statement}
          </div>
        </>
      ) : (
        <pre
          style={{
            fontFamily: 'var(--font-mono)',
            fontSize: 13,
            padding: '12px 14px',
            background: 'var(--paper-100)',
            borderRadius: 6,
            whiteSpace: 'pre-wrap',
            wordBreak: 'break-word',
            margin: 0,
          }}
        >
          {hit.canonical_statement}
        </pre>
      )}
    </Link>
  );
}

function StatusPill({ status }: { status: string }) {
  const bg =
    status === 'Verified'
      ? 'var(--olive-100)'
      : status === 'Pending'
      ? 'var(--terracotta-100)'
      : 'var(--paper-100)';
  return (
    <span
      style={{
        padding: '1px 8px',
        borderRadius: 999,
        background: bg,
        color: 'var(--ink-700)',
      }}
    >
      {status}
    </span>
  );
}
