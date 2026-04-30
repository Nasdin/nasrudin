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

function TheoremView({ thm }: { thm: Theorem }) {
  const idHex = bytesToHex(thm.id);
  // Prefer LaTeX for the statement display; fall back to the canonical
  // prefix-form string so we always render something.
  const stmt = thm.latex ?? thm.canonical_statement;
  // Phase 9 stores the verified Lean source directly on the row.
  const proofTerm = thm.lean_source || '-- not yet verified';
  const parentHexes = (thm.parents ?? []).map(bytesToHex);
  // ChainVerified = sound by construction + provisional. Show the
  // "Verify with Lake" button so the user can promote to LakeVerified
  // on demand (P-Task 4 / manual_verify endpoint).
  const showVerifyButton =
    thm.status === 'Verified' &&
    (thm.verification_tactic === 'chain_replay' || thm.verification_tactic === 'worker_claim');
  // Cascaded rejections carry an `ancestor_rejected:` reason from
  // engine/crates/api/src/reverify.rs::cascade_reject.
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
          <h1 className="thm-name" style={{ margin: 0 }}>
            {idHex}
          </h1>
          <SaveButton theoremIdHex={idHex} />
        </div>
        <div className="thm-statement-block">
          <div className="thm-statement-big">
            <MathExpr source={stmt} block />
          </div>
        </div>
        <div className="thm-section">
          <h3>Lean 4 proof</h3>
          <div className="thm-proof-bar">
            <span>{idHex}.lean</span>
            <button
              type="button"
              className="copy"
              onClick={() => navigator.clipboard.writeText(proofTerm)}
            >
              Copy
            </button>
          </div>
          <ProofBlock source={proofTerm} />
          {showVerifyButton && (
            <div style={{ marginTop: 24 }}>
              <VerifyWithLakeButton theoremIdHex={idHex} />
            </div>
          )}
        </div>
        <div className="thm-section">
          <h3>Proof lineage</h3>
          <LineageList parents={parentHexes} />
        </div>
      </div>
      <aside className="thm-side">
        <h4>Provenance</h4>
        <ul className="meta-list">
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
        </ul>
      </aside>
    </div>
  );
}
