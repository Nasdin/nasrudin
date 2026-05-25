import { Link } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { apiFetch } from '~/lib/api';
import { collectUpstreamRefs, type UpstreamRef } from '~/lib/statementToLatex';

interface UpstreamRefsBlockProps {
  canonical: string;
}

// Server response shape from `GET /api/resolve/{qualifier}`. Discriminated
// union; see engine/crates/api/src/handlers/resolve.rs.
type ResolveResult =
  | { kind: 'theorem'; id: string; domain: string; source: string; verification_tactic: string | null }
  | { kind: 'axiom'; name: string; domain: string; description: string }
  | { kind: 'none' };

function useResolveQualifier(qualifier: string) {
  return useQuery<ResolveResult>({
    queryKey: ['resolve', qualifier],
    queryFn: () =>
      apiFetch<ResolveResult>(
        `/api/resolve/${encodeURIComponent(qualifier)}`,
      ),
    staleTime: 30 * 60_000,
    retry: false,
  });
}

// Per-row: one /api/resolve lookup that the backend answers either with
// a theorem id (→ in-app /theorem/$id), an axiom name (→ /axiom/$name),
// or nothing (→ plain text). The query fires after the parent mounts,
// not during the TanStack Start route-load resolver, so the small batch
// of parallel lookups never races the $_TSR hydration barrier.
function DepRow({ r }: { r: UpstreamRef }) {
  const q = useResolveQualifier(r.qualifier);
  const data = q.data;

  const inner = (() => {
    if (q.isLoading) {
      return <span className="thm-deps-name thm-deps-pending">{r.name}</span>;
    }
    if (data?.kind === 'theorem') {
      return (
        <Link
          to="/theorem/$id"
          params={{ id: data.id }}
          className="thm-deps-name thm-deps-name-theorem"
          title={`Open theorem: ${r.qualifier}`}
        >
          {r.name}
        </Link>
      );
    }
    if (data?.kind === 'axiom') {
      return (
        <Link
          to="/axiom/$name"
          params={{ name: data.name }}
          className="thm-deps-name thm-deps-name-axiom"
          title={data.description || r.qualifier}
        >
          {r.name}
          <span className="thm-deps-kind" aria-hidden="true">
            {' '}def
          </span>
        </Link>
      );
    }
    // kind === 'none' or query errored — plain text. No fake link.
    return (
      <span className="thm-deps-name thm-deps-name-unknown" title={r.qualifier}>
        {r.name}
      </span>
    );
  })();

  return (
    <div className="thm-deps-row">
      {inner}
      <span className="thm-deps-ns">{r.namespace}</span>
    </div>
  );
}

// "Built from" — sits directly below the rendered statement and answers
// the question the user actually has after reading the theorem: "OK, but
// what is `causalCharacter`? What is `spatialPart`?"
//
// Each row hits `/api/resolve/{qualifier}` and the backend returns one
// of three answers:
//
//   theorem  → in-app <Link to="/theorem/$id">
//   axiom    → in-app <Link to="/axiom/$name">
//   none     → plain text (the dependency is an upstream type / instance
//              we don't have in our corpus — no fake link)
//
// We deliberately do NOT render the parent-hash SHA list, and we don't
// fall back to a GitHub search either. Both produce dead-end clicks
// that erode trust in the page; better to honestly render unmatched
// dependencies as text than to pretend they go somewhere.
export function UpstreamRefsBlock({ canonical }: UpstreamRefsBlockProps) {
  const refs = collectUpstreamRefs(canonical);

  if (refs.length === 0) return null;

  return (
    <div className="thm-deps">
      <div className="thm-deps-head">
        <span>Built from</span>
        <span className="thm-deps-count">
          {refs.length} upstream {refs.length === 1 ? 'definition' : 'definitions'}
        </span>
      </div>
      <div className="thm-deps-grid">
        {refs.map((r) => (
          <DepRow key={r.qualifier} r={r} />
        ))}
      </div>
    </div>
  );
}
