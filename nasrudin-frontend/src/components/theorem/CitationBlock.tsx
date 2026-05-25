import { useState } from 'react';

interface CitationBlockProps {
  idHex: string;
  /** Lean qualifier when imported; null for GA-derived rows. */
  importedFrom: string | null;
  /** Humanised title shown as the page heading. */
  displayTitle: string;
  domain: string;
  /** ISO-8601 verification timestamp from the theorem row. */
  verifiedAt: string | null;
  /** verification_tactic from the API. */
  verificationTactic: string | null;
}

// "Cite this theorem" — generates two ready-to-paste citation forms
// (plain text and BibTeX) for a theorem, with one-click Copy buttons.
// A visiting professor who wants to reference a Nasrudin-verified
// result in a paper or a wiki can paste from here without having to
// hand-assemble the citation each time.
export function CitationBlock({
  idHex,
  importedFrom,
  displayTitle,
  domain,
  verifiedAt,
  verificationTactic,
}: CitationBlockProps) {
  const [copied, setCopied] = useState<null | 'text' | 'bibtex'>(null);

  const year = verifiedAt ? new Date(verifiedAt).getFullYear() : new Date().getFullYear();
  const dateStr = verifiedAt
    ? new Date(verifiedAt).toISOString().slice(0, 10)
    : 'unverified';
  const url = `https://nasrudin.org/theorem/${idHex}`;
  const note = verificationTactic === 'imported'
    ? `imported from ${importedFrom ?? 'PhysLean'}, formally verified by Lean 4 kernel`
    : `genetically derived, formally verified by Lean 4 kernel (tactic: ${verificationTactic ?? 'unknown'})`;

  const textCitation =
    `${displayTitle} (Nasrudin theorem ${idHex.slice(0, 8)}). ` +
    `Domain: ${domain}. ${note}. Retrieved ${dateStr} from ${url}.`;

  const bibKey = `nasrudin${idHex.slice(0, 8)}`;
  const bibtex = `@misc{${bibKey},
  title        = {{${displayTitle}}},
  author       = {Nasrudin Corpus},
  year         = {${year}},
  note         = {${note}},
  howpublished = {\\url{${url}}},
  key          = {Nasrudin theorem ${idHex.slice(0, 8)}}
}`;

  function copy(which: 'text' | 'bibtex', value: string) {
    navigator.clipboard.writeText(value).then(
      () => {
        setCopied(which);
        setTimeout(() => setCopied((c) => (c === which ? null : c)), 1800);
      },
      () => {},
    );
  }

  return (
    <div className="thm-section">
      <h3>Cite this theorem</h3>
      <div className="citation-block">
        <div className="citation-row">
          <div className="citation-label">Plain text</div>
          <pre className="citation-text">{textCitation}</pre>
          <button
            type="button"
            className="copy"
            onClick={() => copy('text', textCitation)}
          >
            {copied === 'text' ? '✓ Copied' : 'Copy'}
          </button>
        </div>
        <div className="citation-row">
          <div className="citation-label">BibTeX</div>
          <pre className="citation-text citation-text-mono">{bibtex}</pre>
          <button
            type="button"
            className="copy"
            onClick={() => copy('bibtex', bibtex)}
          >
            {copied === 'bibtex' ? '✓ Copied' : 'Copy'}
          </button>
        </div>
      </div>
    </div>
  );
}
