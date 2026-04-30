import { useLandingStats } from '~/lib/queries';

function prettyDomain(d: string): string {
  return d.replace(/_/g, ' ');
}

export function NetworkBreakdown() {
  const stats = useLandingStats();
  const rows = stats.data?.by_domain_24h ?? [];
  const max = rows.reduce((m, r) => (r.count > m ? r.count : m), 0);

  return (
    <div className="network-breakdown">
      <h4 className="network-breakdown-title">Verified in last 24h, by domain</h4>
      {rows.length === 0 ? (
        <p className="network-breakdown-empty">
          {stats.isLoading ? 'Loading…' : 'No verifications yet in the last 24 hours.'}
        </p>
      ) : (
        rows.map((row) => {
          const pct = max > 0 ? (row.count / max) * 100 : 0;
          return (
            <div className="network-breakdown-row" key={row.domain}>
              <span className="network-breakdown-domain">{prettyDomain(row.domain)}</span>
              <div className="network-breakdown-bar">
                <div
                  className="network-breakdown-fill"
                  style={{ width: `${pct.toFixed(1)}%` }}
                />
              </div>
              <span className="network-breakdown-count">{row.count.toLocaleString()}</span>
            </div>
          );
        })
      )}
    </div>
  );
}
