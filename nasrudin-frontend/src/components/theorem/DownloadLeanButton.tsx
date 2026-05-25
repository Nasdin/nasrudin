import { useState } from 'react';
import { fetchPhysleanSource } from '~/lib/physleanSource';

interface DownloadLeanButtonProps {
  idHex: string;
  /** Inline Lean source for GA-derived theorems. Empty string for
   *  imported theorems — we fetch from PhysLean on click instead. */
  leanSource: string;
  /** Original Lean qualifier (e.g. `Lorentz.Vector.timelike_time_dominates_space`)
   *  if this theorem was imported. */
  importedFrom: string | null;
}

// Anonymous, always-visible "Download .lean" button.
//
// Two code paths:
//
//   - GA-derived theorem with non-empty `lean_source`: download the inline
//     source verbatim. No network call. Fast.
//
//   - Imported PhysLean theorem with empty `lean_source`: fetch the
//     declaration block from PhysLean's GitHub on click. The same
//     `fetchPhysleanSource` the TrustPanel uses — cached, so a click in
//     the TrustPanel and then a download click here reuse the result.
//
// In both cases we synthesise a header at the top of the .lean file so
// the downloaded artifact carries provenance (theorem id, source name,
// URL) without the user needing to remember where it came from.
export function DownloadLeanButton({
  idHex,
  leanSource,
  importedFrom,
}: DownloadLeanButtonProps) {
  const [status, setStatus] = useState<'idle' | 'fetching' | 'done' | 'error'>(
    'idle',
  );

  async function handleClick() {
    setStatus('fetching');
    try {
      let body: string;
      let filename: string;
      if (leanSource && leanSource.trim().length > 0) {
        body = withHeader(leanSource, idHex, importedFrom, null);
        filename = `${idHex}.lean`;
      } else if (importedFrom) {
        const result = await fetchPhysleanSource(importedFrom);
        const snippet = result?.declarationSnippet ?? result?.source ?? null;
        if (!snippet) {
          setStatus('error');
          return;
        }
        body = withHeader(snippet, idHex, importedFrom, result?.fromUrl ?? null);
        filename = `${importedFrom.replaceAll('.', '_')}.lean`;
      } else {
        // GA-derived but no source — shouldn't happen on verified rows,
        // but fall through with a stub so the user gets *something*.
        body = withHeader('-- no Lean source on file', idHex, null, null);
        filename = `${idHex}.lean`;
      }
      triggerDownload(body, filename);
      setStatus('done');
      setTimeout(() => setStatus((s) => (s === 'done' ? 'idle' : s)), 1800);
    } catch {
      setStatus('error');
    }
  }

  const label =
    status === 'fetching' ? 'Fetching…'
      : status === 'done' ? '✓ Downloaded'
      : status === 'error' ? 'Failed — try Show Lean source'
      : 'Download .lean';

  return (
    <button
      type="button"
      className="btn btn-secondary download-lean-btn"
      onClick={handleClick}
      disabled={status === 'fetching'}
      aria-label="Download Lean 4 proof source"
    >
      <span aria-hidden="true">↓</span> {label}
    </button>
  );
}

function withHeader(
  body: string,
  idHex: string,
  importedFrom: string | null,
  upstreamUrl: string | null,
): string {
  const lines = [
    '-- ────────────────────────────────────────────────────────────',
    `-- Nasrudin theorem ${idHex}`,
    '-- https://nasrudin.org/theorem/' + idHex,
  ];
  if (importedFrom) {
    lines.push(`-- Imported from PhysLean: ${importedFrom}`);
  }
  if (upstreamUrl) {
    lines.push(`-- Upstream source: ${upstreamUrl}`);
  }
  lines.push(`-- Downloaded ${new Date().toISOString()}`);
  lines.push('-- ────────────────────────────────────────────────────────────');
  lines.push('');
  return lines.join('\n') + body;
}

function triggerDownload(body: string, filename: string) {
  const blob = new Blob([body], { type: 'text/plain;charset=utf-8' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}
