import { createFileRoute, Link } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useUserSponsorship, useContributors, type SponsorTier } from '~/lib/queries';

export const Route = createFileRoute('/leaderboard')({ loader: async () => null, component: LeaderboardPage });

/// Small colored dot rendered next to a contributor handle when the
/// linked user has an active sponsorship. Subtle by design — no
/// accompanying text, just a 6px circle with a tooltip.
function dotColor(tier: SponsorTier | string | null): string {
  switch (tier) {
    case 'sponsor_100':
    case 'researcher_annual':
      return '#d4a017'; // gold
    case 'sponsor_25':
    case 'researcher_monthly':
      return '#9ca3af'; // silver
    case 'sponsor_5':
      return '#a16207'; // bronze
    case 'sponsor_open':
      return 'var(--olive-700)';
    default:
      return 'var(--olive-700)';
  }
}

function SponsorDot({ userId }: { userId: string | null | undefined }) {
  const { data } = useUserSponsorship(userId ?? null);
  if (!data) return null;
  const hasSubscription = !!data.active_tier;
  const hasDonated = data.lifetime_total_cents > 0;
  if (!hasSubscription && !hasDonated) return null;
  const colour = dotColor(data.active_tier);
  const title = hasSubscription
    ? `Active sponsor (${String(data.active_tier ?? 'sponsor').replace('_', ' ')})`
    : `Donated $${(data.lifetime_total_cents / 100).toFixed(0)} total`;
  return (
    <span
      title={title}
      aria-label={title}
      style={{
        display: 'inline-block',
        width: 6,
        height: 6,
        borderRadius: '50%',
        background: colour,
        marginLeft: 6,
        verticalAlign: 'middle',
      }}
    />
  );
}

function LeaderboardPage() {
  const { data: contributors } = useContributors();
  const ranked = contributors ?? [];
  const [first, second, third] = ranked;
  return (
    <div className="app">
      <AppHeader active="leader" />
      <div className="container-wide">
        <div className="page-head">
          <span className="overline">The network</span>
          <h1>
            Contributors —{' '}
            <em style={{ fontStyle: 'italic', color: 'var(--terracotta-700)', fontWeight: 300 }}>
              credit, not cash.
            </em>
          </h1>
          <p className="lede">
            Users donate compute through workers. Each verified theorem carries the contributor's pseudonym, forever.
          </p>
        </div>
        <div className="page-body">
          <div className="lead-podium">
            {second && (
              <PodiumStep
                step="silver"
                rank="ii"
                handle={second.handle}
                thm={second.theorems_contributed}
                userId={second.user_id}
              />
            )}
            {first && (
              <PodiumStep
                step="gold"
                rank="i"
                handle={first.handle}
                thm={first.theorems_contributed}
                userId={first.user_id}
                marquee
              />
            )}
            {third && (
              <PodiumStep
                step="bronze"
                rank="iii"
                handle={third.handle}
                thm={third.theorems_contributed}
                userId={third.user_id}
              />
            )}
          </div>
          <div className="lead-table-scroll">
          <table className="lead-table">
            <thead>
              <tr>
                <th>Rank</th>
                <th>Contributor</th>
                <th>Workers</th>
                <th style={{ textAlign: 'right' }}>Active</th>
                <th style={{ textAlign: 'right' }}>Theorems</th>
              </tr>
            </thead>
            <tbody>
              {ranked.map((c, i) => (
                <tr key={c.user_id}>
                  <td className="rank-cell">{i + 1}</td>
                  <td className="handle-cell">
                    <Link to="/contributors/$id" params={{ id: c.user_id }}>
                      {c.display_name ?? `@${c.handle}`}
                    </Link>
                    <SponsorDot userId={c.user_id} />
                  </td>
                  <td className="num-cell">{c.worker_count}</td>
                  <td className="num-cell">{c.active_worker_count}</td>
                  <td className="num-cell">{c.theorems_contributed.toLocaleString()}</td>
                </tr>
              ))}
            </tbody>
          </table>
          </div>
          {ranked.length === 0 && (
            <p style={{ color: 'var(--ink-500)', textAlign: 'center', padding: 64 }}>
              No contributors have registered workers yet. Run a node to be the first.
            </p>
          )}
        </div>
      </div>
      <AppFooter />
    </div>
  );
}

function PodiumStep({
  step,
  rank,
  handle,
  thm,
  userId,
  marquee,
}: {
  step: string;
  rank: string;
  handle: string;
  thm: number;
  userId: string;
  marquee?: boolean;
}) {
  return (
    <div
      className={`lead-step ${step}`}
      style={marquee ? { paddingTop: 40, paddingBottom: 40 } : undefined}
    >
      <div className="lead-rank">{rank}</div>
      <Link to="/contributors/$id" params={{ id: userId }}>
        <div className="lead-handle">{handle}</div>
      </Link>
      <div className="lead-num">{thm.toLocaleString()} thm</div>
    </div>
  );
}
