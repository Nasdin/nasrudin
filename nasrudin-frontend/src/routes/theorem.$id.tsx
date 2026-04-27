import { createFileRoute, Link } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { LineageList } from '~/components/theorem/LineageList';
import { ProofBlock } from '~/components/theorem/ProofBlock';
import { ReverifyButton } from '~/components/theorem/ReverifyButton';
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
  const stmt =
    'Latex' in thm.statement
      ? thm.statement.Latex
      : 'Lean' in thm.statement
        ? thm.statement.Lean
        : 'Plain' in thm.statement
          ? thm.statement.Plain
          : '';
  const proofTerm =
    typeof thm.verified === 'object' && 'Verified' in thm.verified
      ? thm.verified.Verified.proof_term
      : '-- not yet verified';
  return (
    <div className="thm-page">
      <div className="thm-main">
        <div className="thm-eyebrow">
          <span className="verified-badge">
            <span className="verified-dot" /> Verified · Lean 4 · re-checked by server
          </span>
          <span>· thm:{thm.id.slice(0, 8)}</span>
          <span>· gen {thm.generation}</span>
        </div>
        <h1 className="thm-name">{thm.id}</h1>
        <div className="thm-statement-block">
          <div className="thm-statement-big">
            <MathExpr source={stmt} block />
          </div>
        </div>
        <div className="thm-section">
          <h3>Lean 4 proof</h3>
          <div className="thm-proof-bar">
            <span>{thm.id}.lean</span>
            <button
              type="button"
              className="copy"
              onClick={() => navigator.clipboard.writeText(proofTerm)}
            >
              Copy
            </button>
          </div>
          <ProofBlock source={proofTerm} />
          <div style={{ marginTop: 24 }}>
            <ReverifyButton />
          </div>
        </div>
        <div className="thm-section">
          <h3>Proof lineage</h3>
          <LineageList parents={thm.parents} />
        </div>
      </div>
      <aside className="thm-side">
        <h4>Provenance</h4>
        <ul className="meta-list">
          <li>
            Generation <strong>{thm.generation}</strong>
          </li>
          <li>
            Depth <strong>{thm.depth}</strong>
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
