import { Link } from '@tanstack/react-router';
import { memo } from 'react';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import type { Theorem } from '~/lib/types';

const linkStyle: React.CSSProperties = {
  textDecoration: 'none',
  color: 'inherit',
  display: 'grid',
};
const monoMetaStyle: React.CSSProperties = { fontFamily: 'var(--font-mono)' };
const domainMetaStyle: React.CSSProperties = {
  letterSpacing: '0.04em',
  textTransform: 'uppercase',
  fontWeight: 600,
};

export const ResultCard = memo(function ResultCard({ thm }: { thm: Theorem }) {
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
      style={linkStyle}
    >
      <div>
        <div className="result-stmt">
          <MathExpr source={stmt} />
        </div>
        <div className="result-name">{idHex}</div>
        <div className="result-meta">
          <span style={monoMetaStyle}>thm:{idHex.slice(0, 8)}</span>
          <span className="dot">·</span>
          <span style={domainMetaStyle}>{thm.domain}</span>
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
});
