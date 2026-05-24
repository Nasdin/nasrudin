import { createFileRoute, Link } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { CascadeAlert } from '~/components/theorem/CascadeAlert';
import { LineageList } from '~/components/theorem/LineageList';
import { ProofBlock } from '~/components/theorem/ProofBlock';
import { SaveButton } from '~/components/theorem/SaveButton';
import { VerificationBadge } from '~/components/theorem/VerificationBadge';
import { VerifyWithLakeButton } from '~/components/theorem/VerifyWithLakeButton';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import { leanToSymbols } from '~/lib/physicsSymbols';
import { useTheorem } from '~/lib/queries';
import type { Theorem } from '~/lib/types';

export const Route = createFileRoute('/theorem/$id')({ component: TheoremPage });

function TheoremPage() {
  const { id } = Route.useParams();
  const { data, isPending, error } = useTheorem(id);

  return (
    <div className="app">
      <AppHeader active="theorem" />
      <div className="container-wide" style={{ paddingTop: 24 }}>
        <div className="crumbs">
          <Link to="/browse">Browse</Link>
          <span className="sep">/</span>
          <span className="current">thm:{id.slice(0, 8)}</span>
        </div>
        {isPending && <p>loading…</p>}
        {error && <p style={{ color: 'var(--danger-500)' }}>Theorem not found.</p>}
        {data && <TheoremView thm={data} />}
      </div>
      <AppFooter />
    </div>
  );
}

// Imported theorems carry the original Lean qualifier in
// origin_payload.Imported.source. Pull it out so we can use it as the
// page heading instead of the opaque 16-hex theorem id.
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

function TheoremView({ thm }: { thm: Theorem }) {
  const idHex = bytesToHex(thm.id);
  const importedFrom = importedSource(thm.origin_payload);
  const isImported = thm.verification_tactic === 'imported';
  const displayHeading = importedFrom ? lastSegment(importedFrom) : idHex;
  const parentHexes = (thm.parents ?? []).map(bytesToHex);
  const showVerifyButton =
    thm.status === 'Verified' &&
    (thm.verification_tactic === 'chain_replay' || thm.verification_tactic === 'worker_claim');
  const isCascade =
    thm.status === 'Rejected' && (thm.rejected_reason?.startsWith('ancestor_rejected:') ?? false);

  return (
    <div className="thm-page">
      <div className="thm-main">
        {isCascade && thm.rejected_reason && <CascadeAlert rejectedReason={thm.rejected_reason} />}
        <div className="thm-eyebrow">
          <VerificationBadge
            status={thm.status}
            tactic={thm.verification_tactic}
            submitterTrusted={thm.worker_trusted}
            rejectedReason={thm.rejected_reason}
          />
          <span>· thm:{idHex.slice(0, 8)}</span>
          <span>· gen {thm.generation ?? 0}</span>
        </div>
        <div
          style={{
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'space-between',
            gap: 16,
            flexWrap: 'wrap',
          }}
        >
          <h1
            className="thm-name"
            style={{
              margin: 0,
              fontFamily: isImported ? 'var(--font-mono)' : undefined,
              fontSize: isImported ? 28 : undefined,
              wordBreak: 'break-word',
            }}
          >
            {displayHeading}
          </h1>
          <SaveButton theoremIdHex={idHex} />
        </div>
        {importedFrom && (
          <div
            style={{
              marginTop: 4,
              fontFamily: 'var(--font-mono)',
              fontSize: 13,
              color: 'var(--ink-500)',
              wordBreak: 'break-all',
            }}
          >
            {importedFrom}
          </div>
        )}
        <div className="thm-statement-block">
          {thm.latex ? (
            <div className="thm-statement-big">
              <MathExpr source={thm.latex} block />
            </div>
          ) : (
            // No LaTeX = imported PhysLean/Mathlib row OR a GA chain
            // whose emitter never produced LaTeX. KaTeX over the
            // prefix-form string renders garbled "math"; show the raw
            // statement as code instead so the user can actually read
            // the s-expression. PhysLean theorems are the dominant case
            // here (~1,000 rows in the seeded corpus).
            <pre
              style={{
                fontFamily: 'var(--font-mono)',
                fontSize: 13,
                lineHeight: 1.55,
                padding: '20px 24px',
                background: 'var(--paper-100)',
                border: '1px solid var(--paper-300)',
                borderRadius: 8,
                overflow: 'auto',
                whiteSpace: 'pre-wrap',
                wordBreak: 'break-word',
              }}
            >
              {leanToSymbols(thm.canonical_statement)}
            </pre>
          )}
        </div>
        {(thm.lean_source || !isImported) && (
          <div className="thm-section">
            <h3>Lean 4 proof</h3>
            <div className="thm-proof-bar">
              <span>{idHex}.lean</span>
              <button
                type="button"
                className="copy"
                onClick={() =>
                  navigator.clipboard.writeText(thm.lean_source || '-- not yet verified')
                }
              >
                Copy
              </button>
            </div>
            <ProofBlock source={thm.lean_source || '-- not yet verified'} />
            {showVerifyButton && (
              <div style={{ marginTop: 24 }}>
                <VerifyWithLakeButton theoremIdHex={idHex} />
              </div>
            )}
          </div>
        )}
        {isImported && !thm.lean_source && (
          <div className="thm-section">
            <h3>Source</h3>
            <p style={{ color: 'var(--ink-600)', lineHeight: 1.6 }}>
              This theorem was imported from{' '}
              <strong>
                {thm.engine_git_sha === 'physlean'
                  ? 'PhysLean'
                  : importedFrom?.startsWith('PhysLean')
                  ? 'PhysLean'
                  : 'Mathlib'}
              </strong>
              . The original Lean 4 declaration{' '}
              <code style={{ fontFamily: 'var(--font-mono)', fontSize: 13 }}>{importedFrom}</code>{' '}
              is part of the upstream library and is accepted by Lean's kernel there. Nasrudin
              indexes it so GA-discovered chains that depend on it can reference a real Lean
              identifier; we do not re-prove it locally.
            </p>
          </div>
        )}
        <div className="thm-section">
          <h3>Proof lineage</h3>
          <LineageList parents={parentHexes} />
        </div>
      </div>
      <aside className="thm-side">
        <h4>Provenance</h4>
        <ul className="meta-list">
          <li>
            Worker{' '}
            <strong style={{ fontFamily: 'var(--font-mono)' }}>{thm.contributor_id}</strong>
          </li>
          {thm.user_email && (
            <li>
              User <strong style={{ fontFamily: 'var(--font-mono)' }}>{thm.user_email}</strong>
            </li>
          )}
          <li>
            Generation <strong>{thm.generation ?? 0}</strong>
          </li>
          <li>
            Depth <strong>{thm.depth ?? 0}</strong>
          </li>
          <li>
            Domain <strong>{thm.domain}</strong>
          </li>
          <li>
            Created <strong>{new Date(thm.created_at).toLocaleString()}</strong>
          </li>
          <li>
            Full ID{' '}
            <strong style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>{idHex}</strong>
          </li>
        </ul>
      </aside>
    </div>
  );
}
