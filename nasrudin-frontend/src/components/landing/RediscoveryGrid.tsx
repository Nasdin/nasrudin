import { FEATURED_REDISCOVERIES } from '~/lib/featured';
import { Math as MathExpr } from '~/lib/katex';

export function RediscoveryGrid() {
  return (
    <div className="rediscover-grid">
      {FEATURED_REDISCOVERIES.map((r) => (
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
