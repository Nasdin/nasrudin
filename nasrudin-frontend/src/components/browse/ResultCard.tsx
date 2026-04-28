import { Link } from '@tanstack/react-router';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import type { Theorem } from '~/lib/types';

export function ResultCard({ thm }: { thm: Theorem }) {
  // Phase 9 schema: prefer LaTeX for math rendering; fall back to canonical
  // (prefix-form) statement so the card always shows something.
  const stmt = thm.latex ?? thm.canonical_statement;
  const idHex = bytesToHex(thm.id);
  const isVerified = thm.status === 'Verified';
  return (
    <Link
      to="/theorem/$id"
      params={{ id: idHex }}
      className="result-card"
      style={{ textDecoration: 'none', color: 'inherit', display: 'grid' }}
    >
      <div>
        <div className="result-stmt">
          <MathExpr source={stmt} />
        </div>
        <div className="result-name">{idHex}</div>
        <div className="result-meta">
          <span style={{ fontFamily: 'var(--font-mono)' }}>thm:{idHex.slice(0, 8)}</span>
          <span className="dot">·</span>
          <span style={{ letterSpacing: '0.04em', textTransform: 'uppercase', fontWeight: 600 }}>
            {thm.domain}
          </span>
          <span className="dot">·</span>
          <span>gen {thm.generation ?? 0}</span>
          <span className="dot">·</span>
          <span>depth {thm.depth ?? 0}</span>
        </div>
      </div>
      <div className="result-side">
        <div className="verified-badge">
          <span className="verified-dot" /> {isVerified ? 'Verified' : thm.status}
        </div>
      </div>
    </Link>
  );
}
