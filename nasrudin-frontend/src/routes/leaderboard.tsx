import { createFileRoute } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useWorkers } from '~/lib/queries';

export const Route = createFileRoute('/leaderboard')({ component: LeaderboardPage });

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
          <table className="lead-table">
            <thead>
              <tr>
                <th>Rank</th>
                <th>Worker</th>
                <th>Host</th>
                <th style={{ textAlign: 'right' }}>Theorems</th>
                <th style={{ textAlign: 'right' }}>Status</th>
                <th style={{ textAlign: 'right' }}>Last seen</th>
              </tr>
            </thead>
            <tbody>
              {ranked.map((w, i) => (
                <tr key={w.id}>
                  <td className="rank-cell">{i + 1}</td>
                  <td className="handle-cell">{w.id}</td>
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
