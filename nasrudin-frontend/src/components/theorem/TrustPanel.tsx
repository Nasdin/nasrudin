import { useState } from 'react';
import { physleanLinks, usePhysleanSource } from '~/lib/physleanSource';
import { WhatIsLean } from './WhatIsLean';

interface TrustPanelProps {
  importedFrom: string | null;
  /** True when every parent of this theorem is itself an upstream
   *  PhysLean / Mathlib definition rather than a GA-derived row.
   *  Drives the wording in the trust list. */
  allParentsUpstream: boolean;
}

// A panel that answers the question a visiting professor actually has:
// "Why should I trust this?" The previous "Proof lineage" section answered
// the question only a Lean expert had: "What are the SHA-256 hashes of the
// dependent theorems?". For an imported PhysLean theorem the right trust
// story is upstream attestation + ability to verify yourself.
export function TrustPanel({ importedFrom, allParentsUpstream }: TrustPanelProps) {
  const [showSource, setShowSource] = useState(false);
  const links = importedFrom ? physleanLinks(importedFrom) : null;
  const sourceQ = usePhysleanSource(showSource ? importedFrom : null);

  if (!importedFrom || !links) return null;

  return (
    <div className="trust-panel">
      <h3>
        Trusted because <WhatIsLean />
      </h3>
      <ul className="trust-list">
        <li>
          <span className="trust-mark" aria-hidden="true">
            ✓
          </span>
          <div>
            <strong>Imported from PhysLean.</strong> PhysLean is the open-source Lean 4 physics
            library. The declaration <code className="mono-pill">{importedFrom}</code> is part of
            the upstream tree.
          </div>
        </li>
        <li>
          <span className="trust-mark" aria-hidden="true">
            ✓
          </span>
          <div>
            <strong>Re-checked by Lean&nbsp;4’s kernel.</strong> Every theorem in PhysLean is
            verified by Lean 4’s small trusted kernel on each upstream build — the same kernel used
            to verify theorems in Mathlib, the largest formal-math library in existence.
          </div>
        </li>
        <li>
          <span className="trust-mark" aria-hidden="true">
            ✓
          </span>
          <div>
            <strong>Built atop upstream PhysLean / Mathlib.</strong>{' '}
            {allParentsUpstream
              ? 'Every named dependency in the statement above is itself an upstream PhysLean / Mathlib definition — no GA-derived link in the chain.'
              : 'Mix of upstream PhysLean definitions and Nasrudin-discovered chains. See the "Built from" list above for the named references.'}
          </div>
        </li>
        <li>
          <span className="trust-mark" aria-hidden="true">
            ✓
          </span>
          <div>
            <strong>Reproducible in ~30&nbsp;seconds.</strong>{' '}
            <code className="mono-pill">
              git clone https://github.com/HEPLean/PhysLean &amp;&amp; cd PhysLean &amp;&amp; lake
              exe cache get &amp;&amp; lake build
            </code>
            . If the build succeeds, Lean has rechecked this theorem on your own machine.
          </div>
        </li>
      </ul>

      <div className="trust-actions">
        <a
          href={links.searchUrl}
          target="_blank"
          rel="noreferrer noopener"
          className="btn btn-secondary"
        >
          View on GitHub ↗
        </a>
        <button type="button" className="btn btn-ghost" onClick={() => setShowSource((v) => !v)}>
          {showSource ? 'Hide' : 'Show'} Lean source
        </button>
      </div>

      {showSource && (
        <div className="trust-source">
          {sourceQ.isLoading && <div className="trust-source-status">Fetching from PhysLean…</div>}
          {sourceQ.error && (
            <div className="trust-source-status">
              Could not load source. Try the{' '}
              <a href={links.searchUrl} target="_blank" rel="noreferrer noopener">
                GitHub search link
              </a>{' '}
              instead.
            </div>
          )}
          {sourceQ.data?.declarationSnippet && (
            <>
              <div className="trust-source-bar">
                <span>{links.declaration}</span>
                <div className="trust-source-bar-actions">
                  <button
                    type="button"
                    className="copy"
                    onClick={() =>
                      navigator.clipboard.writeText(sourceQ.data?.declarationSnippet ?? '')
                    }
                  >
                    Copy
                  </button>
                  <a
                    href={sourceQ.data.fromUrl}
                    target="_blank"
                    rel="noreferrer noopener"
                    className="copy"
                  >
                    Raw file ↗
                  </a>
                </div>
              </div>
              <pre className="trust-source-pre">{sourceQ.data.declarationSnippet}</pre>
            </>
          )}
          {sourceQ.data && !sourceQ.data.declarationSnippet && (
            <div className="trust-source-status">
              Found PhysLean source file but couldn’t pinpoint the{' '}
              <code className="mono-pill">{links.declaration}</code> declaration. Open the{' '}
              <a href={sourceQ.data.fromUrl} target="_blank" rel="noreferrer noopener">
                raw file
              </a>{' '}
              and search for the name.
            </div>
          )}
        </div>
      )}

    </div>
  );
}
