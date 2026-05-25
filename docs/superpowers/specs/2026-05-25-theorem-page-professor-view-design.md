# Theorem page — "Professor View" redesign

**Date:** 2026-05-25
**Author:** brainstormed with Claude, approved by Nasrudin
**Status:** approved, ready to ship

## Problem

A visiting math/physics professor lands on `/theorem/<id>` and sees:

1. A Lean identifier as the title (`mem_iff_mem_toMultiset`).
2. The statement as a raw prefix-form AST (`(pi α1 v:<sort> ...)`). KaTeX render count: **0**.
3. A "Proof lineage" section that's six strikethrough hashes labeled
   "(axiom or upstream reference — no theorem row)" — unclickable, untrustworthy.
4. No way to download the `.lean` file (block is gated on `lean_source` being
   non-empty; imports have `lean_source = ""`).
5. No explanation of what Lean / PhysLean is or why this is trustworthy.
6. Domain tag buried in the sidebar.

Same problems leak onto the landing page:

- "Live · just verified" card falls back to a monospaced Lean qualifier when
  `latex` is null (which is true for 100 % of the seeded corpus's imports).
- "Every theorem. Every proof." table cuts off the statement column at a
  narrow viewport because `.browser-stmt` is `white-space: nowrap; overflow:
  hidden; text-overflow: ellipsis;` and the table itself has no horizontal
  scroll.

## Goal

A first-time visitor — bachelor's-degree math, no Lean background — should
understand within 60 seconds:

1. What this theorem claims, in plain English.
2. What the math actually says, rendered with KaTeX.
3. Where it came from (imported from PhysLean / discovered by the GA), who
   the author is, and why it's trustworthy.
4. How to read or download the actual Lean proof.

A Lean expert should still be able to see the kernel form on demand.

## Design

### Components, build order

**1. `statementToLatex(canonical_statement)`** — pure TS function in
`nasrudin-frontend/src/lib/statementToLatex.ts`.

Parses the prefix-form Lean AST (`(pi ...)`, `(@ f a)`, `(-> A B)`, `(<-> A B)`,
`(= a b)`, `v:Foo.bar`, `<sort>`, numeric/`Nat`/`Real` literals) and emits
LaTeX. Unsupported nodes fall back to a monospaced inline span. Unit tested
against the actual AST strings returned by `/api/theorems/<id>` for the
representative theorems on the live corpus.

Replaces `<pre>{leanToSymbols(...)}</pre>` in:
- `routes/theorem.$id.tsx`
- `components/landing/HeroLiveTheorem.tsx`
- `components/landing/TheoremBrowser.tsx`

Backend untouched. No reindex.

**2. `leanToHumanTitle(qualified)`** — pure TS function. Turns
`Lorentz.Vector.timelike_time_dominates_space` into
"Timelike vectors dominate space" via:

- Split on `.`, take meaningful tail segments.
- Split snake_case → words.
- Title-case the result.
- Drop boilerplate suffixes (`_def`, `_eq`, `_iff`).

Sidebar still shows the original `importedFrom` qualifier in mono.

**3. `statementToProse(canonical_statement, importedFrom)`** — one-sentence
plain-English summary. Curated lookup table for the highest-signal PhysLean
identifiers (~30 entries cover the top corpus by depth). Template fallback
otherwise:

> "For all `<vars>`, if `<antecedent>` then `<consequent>`."

Rendered in an "In one sentence" callout above the statement.

**4. `DomainBadge`** — promote the domain tag from the sidebar list to a
large pill in the page eyebrow. Map raw enum names to human labels (already
have `DOMAIN_LABEL` in `TheoremBrowser.tsx` — extract to `lib/domains.ts`).
Color-code by category (relativity = ocean, electromagnetism = brass,
quantum = violet, pure-math = ink).

**5. `UpstreamSourcePanel`** — replaces the existing "Source" section for
imported theorems.

- Derives the PhysLean GitHub path from `origin_payload.Imported.source`:
  `Lorentz.Vector.timelike_time_dominates_space` →
  `https://github.com/HEPLean/PhysLean/blob/master/PhysLean/Lorentz/Vector/Basic.lean`
  (last segment is the declaration name; the rest is the file path).
- "View on GitHub ↗" button.
- "Fetch Lean source" button: GETs the raw file via TanStack Query, regex-
  extracts the matching `theorem`/`lemma`/`def`/`abbrev` block, shows it in
  the existing `ProofBlock` with Copy / Download buttons.
- "Verify on your machine" two-line CLI snippet.

**6. `TrustPanel`** — replaces today's "Proof lineage" for imports where every
parent is non-resolvable.

For imported theorems:

```
TRUSTED BECAUSE
─────────────────────────────────────────
✓ Imported from PhysLean v<commit>
  Open-source Lean 4 physics library
✓ Re-checked by Lean 4 kernel on every build
✓ All upstream dependencies (n) are part of the
  same library — see source above
✓ MIT-licensed; you can verify it yourself in
  30 seconds: `lake build` after cloning PhysLean
```

For GA-derived theorems with resolvable parents, render the existing lineage
list but visually as a real tree, not a flat numbered list.

**7. `WhatIsLean`** — small popover linked from "Lean 4" anywhere it appears.
One paragraph: what Lean 4 is, why a Lean-kernel-checked proof is stronger
than a peer-reviewed paper, where to read more.

**8. Sidebar declutter** — visible by default: Domain, Origin (Imported /
Discovered), Created date. Behind a `Tech details ▾` toggle: Worker, Full
ID, Generation, Depth, Verification tactic, engine git sha.

### Home-page fixes (bundled into commit 1)

- `.browser-table { overflow-x: auto; }` and `.browser-stmt { white-space:
  nowrap; overflow-x: auto; }` so the cut-off math becomes scrollable.
- `HeroLiveTheorem` already shows mono qualifier when latex is null —
  unchanged in commit 1; gets replaced by `<MathExpr source={
  statementToLatex(canonical_statement)} />` in commit 2.

### Out of scope

- Server-side `latex` population. Client-side rendering is sufficient for v1
  and avoids a backend migration + reindex of 1,634 rows.
- LLM-generated prose for GA-derived chains. Imports are audience-1; GA-chain
  prose is a separate effort.
- Save-for-later / login-walled features. Page stays anonymous-readable.

## Commits

1. `frontend: home-page table overflow-x` — CSS only, 2 lines.
2. `frontend: AST → LaTeX renderer + render statements everywhere they were
   shown as prefix-form text`.
3. `frontend: humanized headline + DomainBadge hero pill + statementToProse
   "in one sentence" box on theorem page`.
4. `frontend: UpstreamSourcePanel (GitHub link + on-demand source fetch) +
   TrustPanel replaces broken lineage + WhatIsLean tooltip + sidebar
   declutter`.

Each commit is independently shippable. Build + deploy after all four land.

## Verification

- Re-run Playwright against `/theorem/ff5e8e43d2c84e4a` (timelike) and
  `/theorem/ff50dbde90497301` (FourTree.mem_iff_mem_toMultiset). Assert
  KaTeX count > 0, "Trust" panel visible, "View on GitHub" link present,
  Lean source loads on click.
- `just smoke-prod`.
- Visual screenshot diff vs `theorem-current.png`.
