import { useState } from 'react';

// Inline "What is Lean 4?" explainer. Renders as a small "(?)" pill next
// to whatever the caller wraps. On click, expands into a popover paragraph
// aimed at someone who has never heard of Lean and is not going to take
// "machine-checked proof" on faith.
//
// Deliberately not modal — closing it should be one Escape or one click
// outside, but for simplicity (this is a once-per-page educational chip)
// we use a click-to-toggle disclosure pattern rather than a positioned
// popover library.
export function WhatIsLean() {
  const [open, setOpen] = useState(false);
  return (
    <span className="what-is-lean">
      <button
        type="button"
        className="what-is-lean-trigger"
        onClick={() => setOpen((v) => !v)}
        aria-expanded={open}
        aria-label="What is Lean 4?"
      >
        new to Lean&nbsp;4?
      </button>
      {open && (
        <span className="what-is-lean-bubble" role="note">
          <strong>Lean&nbsp;4</strong> is a programming language and theorem prover developed at the
          Lean FRO and Carnegie Mellon University. Mathematicians write theorems in Lean; the
          language’s tiny trusted kernel (a few thousand lines, much smaller than its libraries)
          decides whether each proof is correct. A theorem that Lean accepts has been mechanically
          checked all the way down to the axioms — there is no “the reviewer probably caught the
          mistake” step.
          <br />
          <br />
          PhysLean, the library this theorem ships from, layers physics on top of Mathlib (Lean’s
          general-mathematics library, also kernel-checked).
          <br />
          <br />
          Read more:{' '}
          <a href="https://lean-lang.org/" target="_blank" rel="noreferrer noopener">
            lean-lang.org
          </a>
          {' · '}
          <a
            href="https://leanprover-community.github.io/"
            target="_blank"
            rel="noreferrer noopener"
          >
            Mathlib community
          </a>
          {' · '}
          <a href="https://github.com/HEPLean/PhysLean" target="_blank" rel="noreferrer noopener">
            PhysLean repo
          </a>
        </span>
      )}
    </span>
  );
}
