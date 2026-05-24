import { Link } from '@tanstack/react-router';
import { memo } from 'react';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import { leanToSymbols } from '~/lib/physicsSymbols';
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
const contributorStyle: React.CSSProperties = {
  fontSize: 11,
  color: 'var(--ink-500)',
  fontFamily: 'var(--font-mono)',
};

// Imported PhysLean/Mathlib theorems land in the corpus with `latex: null`
// and a prefix-form `canonical_statement` that's unreadable in raw form.
// Pull the original Lean qualifier (e.g. "PhysLean.Fin.finExtractTwo")
// out of `origin_payload` and use it as the card's primary label —
// that's the bibliographic identifier mathematicians actually search by.
function importedSource(payload: unknown): string | null {
  if (payload == null || typeof payload !== 'object') return null;
  const obj = payload as Record<string, unknown>;
  const inner = obj.Imported as Record<string, unknown> | undefined;
  if (!inner) return null;
  const src = inner.source;
  return typeof src === 'string' ? src : null;
}

function lastSegment(qualified: string): string {
  const parts = qualified.split('.');
  return parts[parts.length - 1] ?? qualified;
}

function truncate(s: string, n: number): string {
  if (s.length <= n) return s;
  return `${s.slice(0, n - 1)}…`;
}

export const ResultCard = memo(function ResultCard({ thm }: { thm: Theorem }) {
  const idHex = bytesToHex(thm.id);
  const isVerified = thm.status === 'Verified';
  const importedFrom = importedSource(thm.origin_payload);
  const displayName = importedFrom ? lastSegment(importedFrom) : null;

  // Three render shapes, in priority order:
  //  1. `latex` present → KaTeX math (GA-discovered + curated theorems)
  //  2. Imported lemma with a Lean name → that name is the headline,
  //     the prefix-form statement collapses into a small code preview.
  //  3. Generic fallback → truncated canonical statement as code.
  // Shape (2) is the common case for the ~1,000 imported PhysLean rows
  // and the one the user was hitting in the audit.
  return (
    <Link
      to="/theorem/$id"
      params={{ id: idHex }}
      className="result-card"
      style={linkStyle}
    >
      <div>
        {thm.latex ? (
          <div className="result-stmt">
            <MathExpr source={thm.latex} />
          </div>
        ) : importedFrom ? (
          <>
            <div className="result-name" style={{ fontSize: 15, fontWeight: 600 }}>
              {displayName}
            </div>
            <div
              style={{
                ...monoMetaStyle,
                fontSize: 11,
                color: 'var(--ink-500)',
                marginTop: 2,
              }}
            >
              {importedFrom}
            </div>
            <div
              style={{
                ...monoMetaStyle,
                fontSize: 11,
                color: 'var(--ink-700)',
                marginTop: 6,
                whiteSpace: 'nowrap',
                overflow: 'hidden',
                textOverflow: 'ellipsis',
                maxWidth: '100%',
              }}
              title={leanToSymbols(thm.canonical_statement)}
            >
              {truncate(leanToSymbols(thm.canonical_statement), 160)}
            </div>
          </>
        ) : (
          <div
            style={{
              ...monoMetaStyle,
              fontSize: 12,
              color: 'var(--ink-700)',
              whiteSpace: 'nowrap',
              overflow: 'hidden',
              textOverflow: 'ellipsis',
              maxWidth: '100%',
            }}
            title={leanToSymbols(thm.canonical_statement)}
          >
            {truncate(leanToSymbols(thm.canonical_statement), 200)}
          </div>
        )}
        <div className="result-name" style={{ marginTop: importedFrom ? 6 : undefined }}>
          {idHex}
        </div>
        <div className="result-meta">
          <span style={monoMetaStyle}>thm:{idHex.slice(0, 8)}</span>
          <span className="dot">·</span>
          <span style={domainMetaStyle}>{thm.domain}</span>
          <span className="dot">·</span>
          <span>gen {thm.generation ?? 0}</span>
          <span className="dot">·</span>
          <span>depth {thm.depth ?? 0}</span>
          {importedFrom && (
            <>
              <span className="dot">·</span>
              <span style={{ color: 'var(--terracotta-700)' }}>imported</span>
            </>
          )}
        </div>
        <div className="result-meta" style={{ marginTop: 4 }}>
          <span style={contributorStyle}>
            Worker: {thm.contributor_id}
          </span>
          {thm.user_email && (
            <>
              <span className="dot" style={{ color: 'var(--ink-400)' }}>·</span>
              <span style={contributorStyle}>
                User: {thm.user_email}
              </span>
            </>
          )}
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
