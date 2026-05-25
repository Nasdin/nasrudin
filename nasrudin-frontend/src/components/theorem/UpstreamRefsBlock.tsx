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

  let nameEl: React.ReactNode;
  let kindLabel: string | null = null;
  let description: string | null = null;

  if (q.isLoading) {
    nameEl = <span className="thm-deps-name thm-deps-pending">{r.name}</span>;
  } else if (data?.kind === 'theorem') {
    kindLabel = 'theorem';
    nameEl = (
      <Link
        to="/theorem/$id"
        params={{ id: data.id }}
        className="thm-deps-name thm-deps-name-theorem"
        title={`Open theorem: ${r.qualifier}`}
      >
        {r.name}
      </Link>
    );
  } else if (data?.kind === 'axiom') {
    kindLabel = 'axiom';
    description = data.description || null;
    nameEl = (
      <Link
        to="/axiom/$name"
        params={{ name: data.name }}
        className="thm-deps-name thm-deps-name-axiom"
        title={data.description || r.qualifier}
      >
        {r.name}
      </Link>
    );
  } else {
    kindLabel = 'definition';
    nameEl = (
      <span className="thm-deps-name thm-deps-name-unknown" title={r.qualifier}>
        {r.name}
      </span>
    );
  }

  return (
    <div className="thm-deps-row">
      <div className="thm-deps-name-line">
        {nameEl}
        {kindLabel && (
          <span className={`thm-deps-kind thm-deps-kind-${kindLabel}`}>
            {kindLabel}
          </span>
        )}
      </div>
      <span className="thm-deps-ns">{r.namespace}</span>
      {description && <span className="thm-deps-desc">{description}</span>}
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
      <p className="thm-deps-explain">
        Every named Lean construct the statement above mentions. Each is
        either a <strong>theorem</strong> Nasrudin has already verified
        (terracotta — click to open), an <strong>axiom</strong> or
        <strong> definition</strong> from upstream PhysLean / Mathlib
        (dark — click for description), or an internal Lean construct
        we don't index separately (muted). The <em>proof</em> of this
        theorem is the chain of inferences Lean&nbsp;4's kernel uses to
        derive the statement from these names; see the Lean source
        section below to inspect that chain.
      </p>
      <div className="thm-deps-grid">
        {refs.map((r) => (
          <DepRow key={r.qualifier} r={r} />
        ))}
      </div>
    </div>
  );
}
