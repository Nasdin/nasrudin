import { createFileRoute, Link } from '@tanstack/react-router';
import { useState } from 'react';
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
import { statementToLatex } from '~/lib/statementToLatex';
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

import { displayLeanName as lastSegment } from '~/lib/leanNames';

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
          <StatementRender thm={thm} />
        </div>
        {(thm.lean_source || !isImported) && (
          <div className="thm-section">
            <h3>Lean 4 proof</h3>
            <div className="thm-proof-bar">
              <span>{idHex}.lean</span>
              <div style={{ display: 'flex', gap: 8 }}>
                <button
                  type="button"
                  className="copy"
                  onClick={() =>
                    navigator.clipboard.writeText(thm.lean_source || '-- not yet verified')
                  }
                >
                  Copy
                </button>
                <button
                  type="button"
                  className="copy"
                  onClick={() => downloadLean(idHex, thm.lean_source || '-- not yet verified')}
                  title="Download as .lean file"
                >
                  Download
                </button>
              </div>
            </div>
            <ProofBlock source={thm.lean_source || '-- not yet verified'} />
            {showVerifyButton && (
              <div style={{ marginTop: 24 }}>
                <VerifyWithLakeButton theoremIdHex={idHex} />
              </div>
            )}
          </div>
        )}
        <ChainStepsSection chainJson={thm.chain_json} />
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
            Worker <strong style={{ fontFamily: 'var(--font-mono)' }}>{thm.contributor_id}</strong>
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

// Render the theorem statement: prefer server-provided `latex`; otherwise
// translate the prefix-form `canonical_statement` to LaTeX on the fly. When
// the translator can't render structurally (`complete: false`) we still
// show the partial LaTeX it produced but expose a "View kernel form" toggle
// so a Lean user can see the raw AST. For truly empty / unparseable input
// we drop straight through to the AST view.
function StatementRender({ thm }: { thm: Theorem }) {
  const [showKernel, setShowKernel] = useState(false);

  const rendered = thm.latex
    ? { latex: thm.latex, complete: true }
    : statementToLatex(thm.canonical_statement);

  const canShowLatex = rendered.latex.trim().length > 0;
  const rawAst = leanToSymbols(thm.canonical_statement);

  return (
    <div>
      {canShowLatex ? (
        <div className="thm-statement-big">
          <MathExpr source={rendered.latex} block />
        </div>
      ) : (
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
          {rawAst}
        </pre>
      )}
      {canShowLatex && (
        <div
          style={{
            display: 'flex',
            alignItems: 'center',
            gap: 12,
            marginTop: 12,
            fontSize: 12,
            color: 'var(--ink-500)',
          }}
        >
          {!rendered.complete && (
            <span title="The translator left some internal bindings as ‘?’ — the kernel form has the full detail.">
              partial render
            </span>
          )}
          <button
            type="button"
            className="copy"
            onClick={() => setShowKernel((v) => !v)}
            aria-expanded={showKernel}
          >
            {showKernel ? 'Hide' : 'View'} Lean kernel form
          </button>
        </div>
      )}
      {canShowLatex && showKernel && (
        <pre
          style={{
            fontFamily: 'var(--font-mono)',
            fontSize: 12,
            lineHeight: 1.55,
            padding: '16px 20px',
            marginTop: 12,
            background: 'var(--paper-100)',
            border: '1px solid var(--paper-300)',
            borderRadius: 8,
            overflow: 'auto',
            whiteSpace: 'pre-wrap',
            wordBreak: 'break-word',
            color: 'var(--ink-700)',
          }}
        >
          {rawAst}
        </pre>
      )}
    </div>
  );
}

function downloadLean(idHex: string, source: string): void {
  const blob = new Blob([source], { type: 'text/plain;charset=utf-8' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = `${idHex}.lean`;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

// The GA chain that produced this theorem, persisted as JSON. Each
// element is a `RuleStep` enum tagged with `kind` (IntroduceAxiom,
// RearrangeEquation, TakePositiveRoot, ...) so the UI can render a
// step-by-step trace of how the theorem was built. Imported PhysLean
// rows have an empty array — they have no chain by construction.
function ChainStepsSection({ chainJson }: { chainJson: unknown }) {
  const [open, setOpen] = useState(false);
  const steps = Array.isArray(chainJson) ? (chainJson as Array<Record<string, unknown>>) : [];
  if (steps.length === 0) return null;
  return (
    <div className="thm-section">
      <h3 style={{ display: 'flex', alignItems: 'center', gap: 12 }}>
        <span>Proof chain</span>
        <span style={{ fontSize: 13, color: 'var(--ink-500)', fontWeight: 400 }}>
          {steps.length} step{steps.length === 1 ? '' : 's'}
        </span>
        <button
          type="button"
          className="copy"
          style={{ marginLeft: 'auto' }}
          onClick={() => setOpen((o) => !o)}
        >
          {open ? 'Hide' : 'Show'}
        </button>
      </h3>
      {open && (
        <ol
          style={{
            display: 'grid',
            gap: 8,
            padding: 0,
            paddingLeft: 24,
            margin: 0,
            counterReset: 'step',
          }}
        >
          {steps.map((step, i) => (
            <li
              key={`step-${i}`}
              style={{
                fontFamily: 'var(--font-mono)',
                fontSize: 13,
                padding: '10px 14px',
                background: 'var(--paper-100)',
                border: '1px solid var(--paper-300)',
                borderRadius: 6,
                wordBreak: 'break-word',
              }}
            >
              <div style={{ color: 'var(--ink-500)', fontSize: 11, marginBottom: 4 }}>
                {typeof step.kind === 'string' ? step.kind : 'step'}
              </div>
              {chainStepSummary(step)}
            </li>
          ))}
        </ol>
      )}
    </div>
  );
}

function chainStepSummary(step: Record<string, unknown>): string {
  const kind = typeof step.kind === 'string' ? step.kind : '';
  switch (kind) {
    case 'IntroduceAxiom':
      return typeof step.axiom_name === 'string' ? step.axiom_name : '(unnamed axiom)';
    case 'IntroduceTheorem':
      return typeof step.theorem_name === 'string' ? step.theorem_name : '(unnamed theorem)';
    case 'SubstituteValue':
      return typeof step.reason === 'string' ? step.reason : 'substitute';
    case 'AlgebraicSimplify':
      return 'algebraic simplify';
    case 'RearrangeEquation':
      return typeof step.description === 'string' ? step.description : 'rearrange equation';
    case 'TakePositiveRoot':
      return '√ (positive root)';
    default:
      return JSON.stringify(step).slice(0, 200);
  }
}
