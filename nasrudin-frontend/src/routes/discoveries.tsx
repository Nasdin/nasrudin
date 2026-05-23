import { createFileRoute, Link } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import {
  recentTheoremsOptions,
  useFeaturedDiscoveries,
  useLandingStats,
  useRecentTheorems,
} from '~/lib/queries';
import { useDiscoveryFeed } from '~/lib/sse';
import type { Theorem } from '~/lib/types';

export const Route = createFileRoute('/discoveries')({
  loader: async ({ context }) => {
    await context.queryClient.ensureQueryData(recentTheoremsOptions(20));
  },
  component: DiscoveriesPage,
});

function timeAgo(iso: string | null): string {
  if (!iso) return '—';
  const ms = Date.now() - new Date(iso).getTime();
  if (ms < 60_000) return `${Math.max(1, Math.round(ms / 1000))}s ago`;
  if (ms < 3_600_000) return `${Math.round(ms / 60_000)}m ago`;
  if (ms < 86_400_000) return `${Math.round(ms / 3_600_000)}h ago`;
  return `${Math.round(ms / 86_400_000)}d ago`;
}

function importedSource(payload: unknown): string | null {
  if (payload == null || typeof payload !== 'object') return null;
  const obj = payload as Record<string, unknown>;
  const inner = obj.Imported as Record<string, unknown> | undefined;
  if (!inner) return null;
  const src = inner.source;
  return typeof src === 'string' ? src : null;
}
function lastSegment(qualified: string): string {
  const parts = qualified.split('.');
  return parts[parts.length - 1] ?? qualified;
}

function RecentRow({ thm }: { thm: Theorem }) {
  const id = bytesToHex(thm.id);
  const importedFrom = importedSource(thm.origin_payload);
  return (
    <Link to="/theorem/$id" params={{ id }} className="disc-recent-row">
      <div>
        {thm.latex ? (
          <div className="disc-recent-stmt">
            <MathExpr source={thm.latex} />
          </div>
        ) : importedFrom ? (
          <div
            className="disc-recent-stmt"
            style={{
              fontFamily: 'var(--font-mono)',
              fontSize: 15,
              fontWeight: 600,
              color: 'var(--ink-800)',
            }}
            title={importedFrom}
          >
            {lastSegment(importedFrom)}
          </div>
        ) : (
          <div
            className="disc-recent-stmt"
            style={{
              fontFamily: 'var(--font-mono)',
              fontSize: 13,
              color: 'var(--ink-700)',
              whiteSpace: 'nowrap',
              overflow: 'hidden',
              textOverflow: 'ellipsis',
              maxWidth: '100%',
            }}
            title={thm.canonical_statement}
          >
            {thm.canonical_statement.slice(0, 140)}
            {thm.canonical_statement.length > 140 ? '…' : ''}
          </div>
        )}
        <div className="disc-recent-meta">
          <strong>thm:{id.slice(0, 8)}</strong>
          <span>· {thm.domain}</span>
          {thm.generation != null && <span>· gen {thm.generation}</span>}
          {thm.depth != null && <span>· depth {thm.depth}</span>}
          {importedFrom && <span style={{ color: 'var(--terracotta-700)' }}>· imported</span>}
        </div>
      </div>
      <div className="disc-recent-side">
        <span className="badge badge-verified">✓ {importedFrom ? 'imported' : 'verified'}</span>
        <div className="disc-recent-time">{timeAgo(thm.verified_at)}</div>
      </div>
    </Link>
  );
}

function DiscoveriesPage() {
  // Live invalidation: any new verified theorem refreshes the recent list.
  useDiscoveryFeed();
  const { data } = useRecentTheorems(20);
  const { data: stats } = useLandingStats();
  const { data: featured } = useFeaturedDiscoveries();
  const recent = data?.theorems ?? [];

  // Honest marquee: show the most-recent *GA-discovered* (non-imported)
  // theorem instead of a static "cycle 4,211" claim. Until the GA
  // actually rediscovers a headline result, the marquee says so.
  const latestGa = recent.find(
    (t) => t.verification_tactic !== 'imported' && t.contributor_id !== 'physlean',
  );

  // Featured rediscoveries from /api/featured. Each carries a real
  // `found` flag — true means a matching theorem actually lives in the
  // corpus, false means the search is still active.
  const rediscoveries = featured ?? [];

  return (
    <div className="app">
      <AppHeader active="discoveries" />

      <section className="disc-hero">
        <div className="container-wide">
          <span className="overline">Discoveries</span>
          <h1>
            Physics, as the corpus <em>finds it.</em>
          </h1>
          <p className="lede">
            A genetic algorithm runs on a small upstream axiom set and tries to evolve
            statements Lean&nbsp;4 will accept. The list below is what it has actually
            verified so far — the corpus is still small and most known physics is still
            unverified here. We don&rsquo;t fabricate results.
          </p>
        </div>
      </section>

      <div className="container-wide page-body">
        <div className="disc-section-head">
          <div>
            <span className="overline disc-overline-live">Live · just verified</span>
            <h2>Most recent verifications</h2>
            <p className="disc-section-sub">
              Every result the corpus accepted in the last few hours. Some are
              GA-discovered chains; many are Mathlib/PhysLean imports the GA can build on.
            </p>
          </div>
          <Link to="/browse" className="btn btn-ghost">
            Browse all
            {stats?.verified_theorems != null
              ? ` ${stats.verified_theorems.toLocaleString()}`
              : ''}{' '}
            →
          </Link>
        </div>

        <div className="disc-recent-list">
          {recent.length === 0 ? (
            <div className="disc-recent-empty">Waiting for the next verification…</div>
          ) : (
            recent.slice(0, 12).map((thm) => <RecentRow key={bytesToHex(thm.id)} thm={thm} />)
          )}
        </div>

        <div className="disc-marquee">
          <div>
            <span className="overline">Latest GA-discovered theorem</span>
            {latestGa ? (
              <>
                <h2>
                  Most recent GA chain:{' '}
                  <em>thm:{bytesToHex(latestGa.id).slice(0, 10)}</em>
                </h2>
                <p>
                  Generation {latestGa.generation ?? 0}, depth {latestGa.depth ?? 0}, domain{' '}
                  <strong>{latestGa.domain}</strong>. Verified{' '}
                  {timeAgo(latestGa.verified_at)}.
                </p>
                <div className="disc-marquee-actions">
                  <Link
                    to="/theorem/$id"
                    params={{ id: bytesToHex(latestGa.id) }}
                    className="btn btn-primary"
                  >
                    Open theorem →
                  </Link>
                  <Link to="/browse" className="btn btn-ghost-light">
                    Browse GA chains
                  </Link>
                </div>
              </>
            ) : (
              <>
                <h2>
                  No GA-discovered theorem yet — <em>search is active.</em>
                </h2>
                <p>
                  The corpus is currently seeded with imported lemmas from PhysLean /
                  Mathlib. The headline physics laws below are real search targets, not
                  past wins; this card will update the moment a worker submits a
                  GA-derived chain that Lean accepts.
                </p>
                <div className="disc-marquee-actions">
                  <Link to="/browse" className="btn btn-primary">
                    Browse corpus →
                  </Link>
                  <Link to="/workers" className="btn btn-ghost-light">
                    See live workers
                  </Link>
                </div>
              </>
            )}
          </div>
          <div className="disc-marquee-stmt">
            {latestGa?.latex ? (
              <MathExpr source={latestGa.latex} />
            ) : (
              <code
                style={{
                  fontFamily: 'var(--font-mono)',
                  fontSize: 18,
                  color: 'var(--paper-50)',
                }}
              >
                {latestGa
                  ? `thm:${bytesToHex(latestGa.id).slice(0, 12)}`
                  : '/* search active */'}
              </code>
            )}
            <span className="disc-marquee-sub">
              {latestGa
                ? `${latestGa.verification_tactic ?? 'verified'} · gen ${latestGa.generation ?? 0}`
                : 'no GA-derived theorem in corpus yet'}
            </span>
          </div>
        </div>

        <div className="disc-section-head disc-section-head-second">
          <div>
            <h2>Featured rediscoveries — search status</h2>
            <p className="disc-section-sub">
              Six named physics results we want the GA to derive. Each card is driven by{' '}
              <code style={{ fontFamily: 'var(--font-mono)' }}>/api/featured</code>, which
              checks whether the corpus contains a matching theorem.{' '}
              <strong>&ldquo;Searching&rdquo; means we have not yet found it.</strong>
            </p>
          </div>
        </div>
        <div className="disc-grid">
          {rediscoveries.map((r) => (
            <div
              key={r.name}
              className={`disc-card ${r.found ? '' : 'is-pending'}`}
            >
              <span className="disc-gen-tag">{r.found ? r.cycle : 'search target'}</span>
              <h3>{r.name}</h3>
              <div className="disc-card-stmt">
                <MathExpr source={r.formula} />
              </div>
              <p className="disc-card-desc">{r.note}</p>
              <div className="disc-card-meta">
                <span>
                  <strong>{r.domain}</strong>
                </span>
                {r.found && <span>{r.elapsed}</span>}
                {r.found && r.proof_lines != null && <span>{r.proof_lines} lines</span>}
              </div>
              {!r.found && (
                <div className="disc-card-pending">— still searching —</div>
              )}
            </div>
          ))}
        </div>
      </div>

      <AppFooter />
    </div>
  );
}
