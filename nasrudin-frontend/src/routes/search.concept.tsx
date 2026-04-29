import { createFileRoute, Link } from '@tanstack/react-router';
import { type FormEvent, useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { Math } from '~/lib/katex';
import { useConceptSearch } from '~/lib/queries';
import type { ConceptHit } from '~/lib/types';

export const Route = createFileRoute('/search/concept')({ component: ConceptSearchPage });

function ConceptSearchPage() {
  const [draft, setDraft] = useState('');
  const [query, setQuery] = useState('');
  const [includePending, setIncludePending] = useState(true);
  const search = useConceptSearch(query, { includePending });

  const onSubmit = (e: FormEvent) => {
    e.preventDefault();
    setQuery(draft.trim());
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

        <form
          onSubmit={onSubmit}
          style={{ display: 'flex', gap: 12, alignItems: 'center', marginBottom: 16 }}
        >
          <input
            type="text"
            value={draft}
            onChange={(e) => setDraft(e.target.value)}
            placeholder="all the equations that have to do with Energy"
            style={{
              flex: 1,
              padding: '10px 14px',
              fontSize: 15,
              fontFamily: 'var(--font-sans)',
              background: 'var(--bg-raised)',
              border: '1px solid var(--paper-200)',
              borderRadius: 'var(--radius-md)',
              color: 'var(--ink-900)',
            }}
          />
          <label
            style={{
              display: 'flex',
              alignItems: 'center',
              gap: 6,
              fontSize: 13,
              color: 'var(--ink-700)',
            }}
          >
            <input
              type="checkbox"
              checked={includePending}
              onChange={(e) => setIncludePending(e.target.checked)}
            />
            include conjectures
          </label>
          <button
            type="submit"
            className="btn btn-primary"
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

        {search.isPending && query && (
          <div style={{ color: 'var(--ink-500)' }}>Searching…</div>
        )}

        {search.data && (
          <div style={{ marginBottom: 12, color: 'var(--ink-500)', fontSize: 13 }}>
            {search.data.hits.length} hit{search.data.hits.length === 1 ? '' : 's'} ·{' '}
            {search.data.took_ms} ms
          </div>
        )}

        {search.data && search.data.hits.length === 0 && query && (
          <div className="card">
            No matches for <em>"{query}"</em>. Try a broader phrase, or toggle
            "include conjectures" if you only see verified rows.
          </div>
        )}

        {search.data &&
          search.data.hits.map((h) => <ConceptHitCard key={h.theorem_id} hit={h} />)}
      </div>
      <AppFooter />
    </div>
  );
}

function ConceptHitCard({ hit }: { hit: ConceptHit }) {
  const stmt = hit.latex ?? hit.canonical_statement;
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
      <div style={{ fontSize: 18 }}>
        <Math source={stmt} block />
      </div>
      {hit.latex && (
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
