import { Link } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { apiFetch } from '~/lib/api';
import type { Theorem } from '~/lib/types';

const NUMERALS = ['i', 'ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii', 'ix', 'x'];

function romanize(n: number): string {
  return NUMERALS[n - 1] ?? String(n);
}

function importedSource(payload: unknown): string | null {
  if (payload == null || typeof payload !== 'object') return null;
  const obj = payload as Record<string, unknown>;
  const inner = obj.Imported as Record<string, unknown> | undefined;
  if (!inner) return null;
  const src = inner.source;
  return typeof src === 'string' ? src : null;
}
import { displayLeanName as lastSegment } from '~/lib/leanNames';

// Each parent is fetched lazily: if /api/theorems/:id resolves we render
// a clickable link with the human label; if it 404s (e.g. PhysLean
// import whose "parent" is an axiom-namespace pointer not promoted to a
// standalone theorem row) we render an inert stub with "not in corpus".
// This replaces the previous behaviour where every parent was a link
// regardless, and ~half of them landed on an empty 404 page.
function LineageRow({ id, idx }: { id: string; idx: number }) {
  const q = useQuery({
    queryKey: ['theorem', id],
    queryFn: () => apiFetch<Theorem>(`/api/theorems/${id}`),
    staleTime: 10 * 60_000,
    retry: false,
  });

  const label = (() => {
    if (q.isLoading) return id;
    if (q.error) return id;
    const imp = importedSource(q.data?.origin_payload);
    if (imp) return lastSegment(imp);
    return id;
  })();

  const resolvable = !q.isLoading && !q.error && !!q.data;

  return (
    <li>
      <span className="lineage-step">{romanize(idx + 1)}.</span>
      {resolvable ? (
        <span>
          <Link to="/theorem/$id" params={{ id }} className="lineage-name">
            {label}
          </Link>
          <span
            style={{
              fontFamily: 'var(--font-mono)',
              fontSize: 11,
              color: 'var(--ink-500)',
              marginLeft: 12,
            }}
          >
            {id}
          </span>
        </span>
      ) : q.isLoading ? (
        <span
          style={{
            fontFamily: 'var(--font-mono)',
            color: 'var(--ink-500)',
          }}
        >
          {id}
        </span>
      ) : (
        // Parent BYTEA exists on the chain but no theorem row backs it.
        // Most common cause: imported PhysLean rows whose `parents` list
        // includes upstream namespace references (axioms, type
        // definitions) that we don't promote into individual theorem
        // rows. We label it explicitly so the user understands clicking
        // wouldn't take them anywhere useful.
        <span
          title="No theorem row for this parent — typically an axiom or upstream-library namespace reference. Not navigable."
          style={{
            fontFamily: 'var(--font-mono)',
            color: 'var(--ink-500)',
            textDecoration: 'line-through',
          }}
        >
          {id}
          <span
            style={{
              marginLeft: 12,
              fontStyle: 'italic',
              color: 'var(--ink-400)',
              textDecoration: 'none',
            }}
          >
            (axiom or upstream reference — no theorem row)
          </span>
        </span>
      )}
    </li>
  );
}

export function LineageList({ parents }: { parents: string[] }) {
  if (parents.length === 0) {
    return <p style={{ color: 'var(--ink-500)' }}>This theorem has no parents — it's an axiom.</p>;
  }
  return (
    <ol className="lineage">
      {parents.map((id, i) => (
        <LineageRow key={id} id={id} idx={i} />
      ))}
    </ol>
  );
}
