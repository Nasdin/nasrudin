import { useFeaturedDiscoveries } from '~/lib/queries';
import { Math as MathExpr } from '~/lib/katex';
import type { Rediscovery } from '~/lib/featured';

export function RediscoveryGrid() {
  const { data: discoveries, isLoading, error } = useFeaturedDiscoveries();

  if (isLoading) {
    return (
      <div className="rediscover-grid">
        {[...Array(6)].map((_, i) => (
          <div key={`loading-${i}`} className="rediscover-card aspirational">
            <div className="rediscover-status pending">○ Loading</div>
            <div className="rediscover-formula">...</div>
            <div className="rediscover-name">Loading...</div>
            <div className="rediscover-domain">...</div>
            <p
              style={{
                fontSize: 13,
                lineHeight: 1.55,
                color: 'var(--ink-700)',
                marginBottom: 16,
              }}
            >
              Loading featured discoveries from corpus...
            </p>
            <div className="rediscover-meta">
              <div>
                <div className="rediscover-meta-label">Discovered at</div>
                <div className="rediscover-meta-val">...</div>
              </div>
              <div>
                <div className="rediscover-meta-label">Status</div>
                <div className="rediscover-meta-val">...</div>
              </div>
            </div>
          </div>
        ))}
      </div>
    );
  }

  if (error || !discoveries) {
    return (
      <div className="rediscover-grid">
        <div className="rediscover-card aspirational" style={{ gridColumn: '1 / -1' }}>
          <div className="rediscover-status pending">○ Error</div>
          <div className="rediscover-name">Failed to load featured discoveries</div>
          <p
            style={{
              fontSize: 13,
              lineHeight: 1.55,
              color: 'var(--ink-700)',
              marginBottom: 16,
            }}
          >
            Unable to fetch discoveries from the corpus. Please try again later.
          </p>
        </div>
      </div>
    );
  }

  // Transform API response to match Rediscovery interface
  const rediscoveries: Rediscovery[] = discoveries.map((d) => ({
    formula: d.formula,
    name: d.name,
    domain: d.domain,
    found: d.found,
    cycle: d.cycle,
    elapsed: d.elapsed,
    ...(d.proof_lines !== undefined ? { proofLines: d.proof_lines } : {}),
    note: d.note,
  }));

  return (
    <div className="rediscover-grid">
      {rediscoveries.map((r) => (
        <div key={r.name} className={`rediscover-card ${r.found ? '' : 'aspirational'}`}>
          <div className={`rediscover-status ${r.found ? 'found' : 'pending'}`}>
            {r.found ? '✓ Rediscovered' : '○ Searching'}
          </div>
          <div className="rediscover-formula">
            <MathExpr source={r.formula} />
          </div>
          <div className="rediscover-name">{r.name}</div>
          <div className="rediscover-domain">{r.domain}</div>
          <p
            style={{
              fontSize: 13,
              lineHeight: 1.55,
              color: 'var(--ink-700)',
              marginBottom: 16,
            }}
          >
            {r.note}
          </p>
          <div className="rediscover-meta">
            <div>
              <div className="rediscover-meta-label">Discovered at</div>
              <div className="rediscover-meta-val">{r.cycle}</div>
            </div>
            <div>
              <div className="rediscover-meta-label">{r.found ? 'Wall time' : 'Status'}</div>
              <div className="rediscover-meta-val">{r.elapsed}</div>
            </div>
            {r.found && r.proofLines !== undefined && (
              <div>
                <div className="rediscover-meta-label">Proof lines</div>
                <div className="rediscover-meta-val">{r.proofLines}</div>
              </div>
            )}
          </div>
        </div>
      ))}
    </div>
  );
}
