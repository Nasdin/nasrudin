import { Link } from '@tanstack/react-router';
import { Math as MathExpr } from '~/lib/katex';
import type { Theorem } from '~/lib/types';

export function ResultCard({ thm }: { thm: Theorem }) {
  const stmt =
    'Latex' in thm.statement
      ? thm.statement.Latex
      : 'Lean' in thm.statement
        ? thm.statement.Lean
        : 'Plain' in thm.statement
          ? thm.statement.Plain
          : '';
  const isVerified = typeof thm.verified !== 'string' && 'Verified' in thm.verified;
  return (
    <Link
      to="/theorem/$id"
      params={{ id: thm.id }}
      className="result-card"
      style={{ textDecoration: 'none', color: 'inherit', display: 'grid' }}
    >
      <div>
        <div className="result-stmt">
          <MathExpr source={stmt} />
        </div>
        <div className="result-name">{thm.id}</div>
        <div className="result-meta">
          <span style={{ fontFamily: 'var(--font-mono)' }}>thm:{thm.id.slice(0, 8)}</span>
          <span className="dot">·</span>
          <span style={{ letterSpacing: '0.04em', textTransform: 'uppercase', fontWeight: 600 }}>
            {thm.domain}
          </span>
          <span className="dot">·</span>
          <span>gen {thm.generation}</span>
          <span className="dot">·</span>
          <span>depth {thm.depth}</span>
        </div>
      </div>
      <div className="result-side">
        <div className="verified-badge">
          <span className="verified-dot" /> {isVerified ? 'Verified' : 'Pending'}
        </div>
      </div>
    </Link>
  );
}
