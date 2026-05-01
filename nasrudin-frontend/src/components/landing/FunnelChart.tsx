import { useLandingStats } from '~/lib/queries';

/// Discard funnel: submitted → verified vs rejected, plus current pending
/// queue depth. Numbers come from the existing `theorems` mirror table —
/// no extra worker plumbing. Each stage is rendered as a horizontal bar
/// normalized to `submitted_24h` so the eye can read the survival rate
/// at a glance.
export function FunnelChart() {
  const stats = useLandingStats();
  const f = stats.data?.funnel_24h;

  if (!f) {
    return (
      <div className="funnel-chart">
        <h4 className="funnel-title">Pipeline funnel · last 24h</h4>
        <p className="funnel-empty">
          {stats.isLoading ? 'Loading…' : 'No pipeline activity yet.'}
        </p>
      </div>
    );
  }

  const submitted = f.submitted_24h;
  // Survival rate: how often Lean accepts a candidate. Computed off
  // (verified + rejected) rather than `submitted` so a tail of pending
  // doesn't drag the percentage down — those candidates haven't been
  // judged yet.
  const judged = f.verified_24h + f.rejected_24h;
  const survival = judged > 0 ? (f.verified_24h / judged) * 100 : 0;

  const rows: Array<{
    label: string;
    count: number;
    accent: 'olive' | 'terracotta' | 'saffron' | 'ink';
    sub: string;
  }> = [
    {
      label: 'Submitted',
      count: f.submitted_24h,
      accent: 'ink',
      sub: 'every worker submission, regardless of outcome',
    },
    {
      label: 'Pending',
      count: f.pending_now,
      accent: 'saffron',
      sub: 'in lake-build queue right now',
    },
    {
      label: 'Verified',
      count: f.verified_24h,
      accent: 'olive',
      sub: 'Lean kernel accepted',
    },
    {
      label: 'Rejected',
      count: f.rejected_24h,
      accent: 'terracotta',
      sub: 'Lean kernel said no',
    },
  ];

  return (
    <div className="funnel-chart">
      <div className="funnel-head">
        <h4 className="funnel-title">Pipeline funnel · last 24h</h4>
        {judged > 0 && (
          <span className="funnel-survival">
            <strong>{survival.toFixed(1)}%</strong> survival rate
          </span>
        )}
      </div>

      <div className="funnel-rows">
        {rows.map((row) => {
          const pct = submitted > 0 ? (row.count / submitted) * 100 : 0;
          return (
            <div key={row.label} className="funnel-row">
              <div className="funnel-row-label">
                <span className="funnel-row-name">{row.label}</span>
                <span className="funnel-row-sub">{row.sub}</span>
              </div>
              <div className="funnel-row-bar">
                <div
                  className={`funnel-row-fill funnel-row-fill--${row.accent}`}
                  style={{ width: `${pct.toFixed(1)}%` }}
                />
              </div>
              <span className="funnel-row-count">{row.count.toLocaleString()}</span>
            </div>
          );
        })}
      </div>

      <p className="funnel-note">
        Most candidates are nonsense. The wise fool knew this.
      </p>
    </div>
  );
}
