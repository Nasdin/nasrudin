import { Link } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { apiFetch } from '~/lib/api';
import { domainPresentation } from '~/lib/domains';
import { leanToHumanTitle } from '~/lib/humanTitle';
import { displayLeanName } from '~/lib/leanNames';

interface UsedByBlockProps {
  idHex: string;
}

interface DependentRow {
  id: string;
  domain: string;
  imported_source: string | null;
  generation: number | null;
  verification_tactic: string | null;
  created_at: string;
}

interface DependentsResponse {
  dependents: DependentRow[];
  total: number;
}

// "Used by" — the inverse of "Built from". Lists theorems whose `parents`
// array contains this theorem's id. For an upstream-style base lemma
// this surfaces the downstream chains that lean on it; for a leaf GA
// discovery it'll usually be empty (which is itself informative — the
// user knows this theorem doesn't have downstream consumers yet).
//
// Same pattern as UpstreamRefsBlock: lazy useQuery after mount so the
// fetch doesn't race the route-load $_TSR teardown. Hidden entirely
// when there are zero dependents to keep the page tight.
export function UsedByBlock({ idHex }: UsedByBlockProps) {
  const q = useQuery<DependentsResponse>({
    queryKey: ['theorem-dependents', idHex],
    queryFn: () =>
      apiFetch<DependentsResponse>(`/api/theorems/${idHex}/dependents`),
    staleTime: 5 * 60_000,
    retry: false,
  });

  if (q.isLoading) {
    return (
      <div className="thm-deps">
        <div className="thm-deps-head">
          <span>Used by</span>
          <span className="thm-deps-count">checking…</span>
        </div>
      </div>
    );
  }
  if (q.error || !q.data || q.data.total === 0) return null;

  const rows = q.data.dependents;

  return (
    <div className="thm-deps">
      <div className="thm-deps-head">
        <span>Used by</span>
        <span className="thm-deps-count">
          {q.data.total} downstream {q.data.total === 1 ? 'theorem' : 'theorems'}
        </span>
      </div>
      <div className="thm-deps-grid">
        {rows.map((r) => (
          <UsedByRow key={r.id} row={r} />
        ))}
      </div>
    </div>
  );
}

function UsedByRow({ row }: { row: DependentRow }) {
  // For imported PhysLean rows, surface the humanised title. For
  // GA-derived theorems with no `imported_source`, fall back to the
  // 8-byte hex id slice — it's at least navigable and unique.
  const human = leanToHumanTitle(row.imported_source);
  const label = human
    || (row.imported_source ? displayLeanName(row.imported_source) : `thm:${row.id.slice(0, 8)}`);
  const ns = row.imported_source
    ? row.imported_source.split('.').slice(0, -1).join('.')
    : domainPresentation(row.domain).label;
  return (
    <div className="thm-deps-row">
      <Link
        to="/theorem/$id"
        params={{ id: row.id }}
        className="thm-deps-name thm-deps-name-theorem"
        title={row.imported_source ?? row.id}
      >
        {label}
      </Link>
      <span className="thm-deps-ns">{ns}</span>
    </div>
  );
}
