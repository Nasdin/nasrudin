import { createFileRoute, Link } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { DomainBadge } from '~/components/theorem/DomainBadge';
import { apiFetch } from '~/lib/api';

export const Route = createFileRoute('/axiom/$name')({ component: AxiomPage });

type Resolve =
  | {
      kind: 'theorem';
      id: string;
      domain: string;
      source: string;
      verification_tactic: string | null;
    }
  | { kind: 'axiom'; name: string; domain: string; description: string }
  | { kind: 'none' };

// Each axiom row lives in the in-memory AxiomStore on the API server, not
// in PG. We surface the same record the "Built from" panel routed us
// from: name, domain, description. There's no separate `/api/axioms/<name>`
// endpoint — we reuse the resolve endpoint that already does single-name
// lookup against the AxiomStore.
function AxiomPage() {
  const { name } = Route.useParams();
  const q = useQuery<Resolve>({
    queryKey: ['resolve', name],
    queryFn: () => apiFetch<Resolve>(`/api/resolve/${encodeURIComponent(name)}`),
    staleTime: 30 * 60_000,
    retry: false,
  });

  return (
    <div className="app">
      <AppHeader active="theorem" />
      <div className="container-wide" style={{ paddingTop: 24 }}>
        <div className="crumbs">
          <Link to="/browse">Browse</Link>
          <span className="sep">/</span>
          <span className="current">axiom:{name}</span>
        </div>
        {q.isLoading && <p>loading…</p>}
        {q.error && <p style={{ color: 'var(--danger-500)' }}>Failed to load axiom.</p>}
        {q.data?.kind === 'axiom' && (
          <AxiomView name={q.data.name} domain={q.data.domain} description={q.data.description} />
        )}
        {q.data?.kind === 'theorem' && (
          // Edge case: the qualifier resolved to a theorem rather than an
          // axiom. Redirect intent — render a tiny "this is actually a
          // theorem" pointer with a Link rather than auto-navigating, so
          // the URL change is explicit / shareable.
          <div className="thm-page">
            <div className="thm-main">
              <p>
                <code style={{ fontFamily: 'var(--font-mono)' }}>{name}</code> is a
                theorem, not an axiom.{' '}
                <Link to="/theorem/$id" params={{ id: q.data.id }}>
                  Open the theorem page →
                </Link>
              </p>
            </div>
          </div>
        )}
        {q.data?.kind === 'none' && (
          <div className="thm-page">
            <div className="thm-main">
              <h1 className="thm-name" style={{ fontFamily: 'var(--font-mono)', fontSize: 28 }}>
                {name}
              </h1>
              <p style={{ color: 'var(--ink-600)', lineHeight: 1.6 }}>
                We don’t have a record of this name in Nasrudin’s axiom
                store. It’s likely an upstream Lean / Mathlib type, instance,
                or hygenic generated identifier that the importer did not
                promote into a standalone record. There’s nothing more to
                see here.
              </p>
              <p>
                <Link to="/browse">Back to corpus →</Link>
              </p>
            </div>
          </div>
        )}
      </div>
      <AppFooter />
    </div>
  );
}

function AxiomView({
  name,
  domain,
  description,
}: {
  name: string;
  domain: string;
  description: string;
}) {
  return (
    <div className="thm-page">
      <div className="thm-main">
        <div className="thm-eyebrow">
          <span className="verified-badge">
            <span className="verified-dot" /> AXIOM · UPSTREAM-INDEXED
          </span>
          <DomainBadge domain={domain} size="md" />
        </div>
        <h1
          className="thm-name"
          style={{ fontFamily: 'var(--font-mono)', fontSize: 28, wordBreak: 'break-word' }}
        >
          {name}
        </h1>
        <div className="thm-prose" role="note" aria-label="Description">
          <span className="thm-prose-eyebrow">Description</span>
          {description || (
            <span style={{ color: 'var(--ink-500)' }}>
              No description on file for this axiom.
            </span>
          )}
        </div>
        <div className="thm-section">
          <h3>What is this?</h3>
          <p style={{ color: 'var(--ink-700)', lineHeight: 1.6 }}>
            This is a definition or axiom Nasrudin imported from the
            upstream Lean / PhysLean / Mathlib corpus. The GA can build new
            theorems on top of it, but Nasrudin doesn’t re-prove it
            locally — the upstream library’s Lean 4 kernel attestation is
            what makes it trustworthy.
          </p>
        </div>
      </div>
      <aside className="thm-side">
        <h4>Provenance</h4>
        <ul className="meta-list">
          <li>
            Domain <strong>{domain}</strong>
          </li>
          <li>
            Source <strong>Upstream Lean library</strong>
          </li>
          <li>
            Full name{' '}
            <strong style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>{name}</strong>
          </li>
        </ul>
      </aside>
    </div>
  );
}
