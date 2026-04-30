import { createFileRoute } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useUserSponsorship, useWorkers, type SponsorTier } from '~/lib/queries';

export const Route = createFileRoute('/leaderboard')({ component: LeaderboardPage });

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
  const { data } = useWorkers();
  const ranked = (data ?? [])
    .slice()
    .sort((a, b) => b.theorems_contributed - a.theorems_contributed);
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
            Workers donate compute. Each verified theorem carries the worker's pseudonym, forever.
          </p>
        </div>
        <div className="page-body">
          <div className="lead-podium">
            {second && (
              <PodiumStep
                step="silver"
                rank="ii"
                handle={second.id}
                thm={second.theorems_contributed}
              />
            )}
            {first && (
              <PodiumStep
                step="gold"
                rank="i"
                handle={first.id}
                thm={first.theorems_contributed}
                marquee
              />
            )}
            {third && (
              <PodiumStep
                step="bronze"
                rank="iii"
                handle={third.id}
                thm={third.theorems_contributed}
              />
            )}
          </div>
          <div className="lead-table-scroll">
          <table className="lead-table">
            <thead>
              <tr>
                <th>Rank</th>
                <th>Worker</th>
                <th>Host</th>
                <th style={{ textAlign: 'right' }}>Theorems</th>
                <th style={{ textAlign: 'right' }}>Reputation</th>
                <th style={{ textAlign: 'right' }}>Status</th>
                <th style={{ textAlign: 'right' }}>Last seen</th>
              </tr>
            </thead>
            <tbody>
              {ranked.map((w, i) => (
                <tr key={w.id}>
                  <td className="rank-cell">{i + 1}</td>
                  <td className="handle-cell">
                    {w.id}
                    <SponsorDot userId={w.owner?.user_id} />
                  </td>
                  <td
                    style={{
                      color: 'var(--ink-500)',
                      fontFamily: 'var(--font-mono)',
                      fontSize: 12,
                    }}
                  >
                    {w.host ?? '—'}
                  </td>
                  <td className="num-cell">{w.theorems_contributed.toLocaleString()}</td>
                  <td className="num-cell">
                    <ReputationCell
                      score={w.reputation_score}
                      revoked={Boolean(w.auto_revoked_at)}
                    />
                  </td>
                  <td
                    className="num-cell"
                    style={{
                      color:
                        String(w.status).toLowerCase() === 'active'
                          ? 'var(--olive-700)'
                          : 'var(--ink-500)',
                    }}
                  >
                    {String(w.status).toLowerCase()}
                  </td>
                  <td className="num-cell" style={{ color: 'var(--ink-500)' }}>
                    {new Date(w.last_seen).toLocaleString()}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
          </div>
          {ranked.length === 0 && (
            <p style={{ color: 'var(--ink-500)', textAlign: 'center', padding: 64 }}>
              No workers have registered yet. Run a node to be the first.
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
  marquee,
}: {
  step: string;
  rank: string;
  handle: string;
  thm: number;
  marquee?: boolean;
}) {
  return (
    <div
      className={`lead-step ${step}`}
      style={marquee ? { paddingTop: 40, paddingBottom: 40 } : undefined}
    >
      <div className="lead-rank">{rank}</div>
      <div className="lead-handle">{handle}</div>
      <div className="lead-num">{thm.toLocaleString()} thm</div>
    </div>
  );
}

/// Reputation column. Colour-codes the EMA score and surfaces an
/// auto-revoked badge when the worker has been kicked off ingest by
/// the spot-check defence. `score` is undefined for legacy rows.
function ReputationCell({ score, revoked }: { score: number | undefined; revoked: boolean }) {
  if (revoked) {
    return (
      <span
        title="Auto-revoked: 5 consecutive spot-check failures"
        style={{
          fontSize: 11,
          padding: '2px 6px',
          borderRadius: 999,
          background: 'var(--danger-50, #fef2f2)',
          color: 'var(--danger-700, #b91c1c)',
          fontWeight: 600,
          letterSpacing: 0.3,
          textTransform: 'uppercase',
        }}
      >
        Revoked
      </span>
    );
  }
  if (score === undefined) {
    return <span style={{ color: 'var(--ink-400)' }}>—</span>;
  }
  const colour =
    score >= 0.9 ? 'var(--olive-700)' : score >= 0.5 ? 'var(--ink-700)' : 'var(--danger-700)';
  return (
    <span
      title={
        score >= 0.9
          ? 'Trusted contributor'
          : score >= 0.5
            ? 'On probation'
            : 'Throttled — close to auto-revoke'
      }
      style={{ color: colour, fontVariantNumeric: 'tabular-nums' }}
    >
      {score.toFixed(2)}
    </span>
  );
}
