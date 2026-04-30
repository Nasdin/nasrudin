# Frontend Mobile Responsiveness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Eliminate layout-shift in `HeroLiveTheorem` and make every route on `nasrudin-frontend` legible/usable at 360px / 480px / 640px / 1024px widths.

**Architecture:** CSS-only changes in `styles.css` (landing + theorem card) and `platform.css` (app shell + platform routes). Possibly small JSX in `HeroLiveTheorem.tsx`. Three-tier breakpoint strategy: existing `≤1024` and `≤640`, plus new `≤480`.

**Tech Stack:** TanStack Start (React + Vite), Biome, vitest, KaTeX, plain CSS with custom-property design tokens.

**Spec reference:** `docs/superpowers/specs/2026-04-30-frontend-mobile-responsive-design.md`

**Verification approach:** This is visual/CSS work. "Tests" are headless-browser checks at the four breakpoint widths via the `gstack` skill (or manual viewport testing in `pnpm dev` if unavailable). For the layout-shift fix specifically, capture before/after screenshots showing the live card across rotations to prove zero pixel movement of surrounding content.

**Dev server:** `just dev-frontend` (runs `pnpm dev` on port 3000).

**General commit guidance:** Each task ends with a commit. Use `frontend:` prefix to match repo style.

---

## File Structure

**Modified:**
- `nasrudin-frontend/src/styles/styles.css` — landing page (hero, sections, theorem card, ticker, all `.landing-*` rules) + adds `≤480` breakpoint, tightens `≤640`.
- `nasrudin-frontend/src/styles/platform.css` — app shell + every platform route's responsive rules.

**Possibly modified (only if skeleton/loaded card structure mismatch found in Task 1):**
- `nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx`

**Read-only references (audit targets):**
- All files in `nasrudin-frontend/src/routes/` and `nasrudin-frontend/src/components/`.

No new files are created. No new dependencies are added. No JS logic changes (timers, queries, state remain identical).

---

## Task 1: Stabilize the live theorem card height (layout-shift fix)

**Goal:** `.theorem-card` occupies identical pixel dimensions across all theorem rotations and across the skeleton state. The hero text column on desktop and the section below on mobile must not move when a new theorem appears.

**Files:**
- Modify: `nasrudin-frontend/src/styles/styles.css` — `.theorem-card-body`, `.theorem-statement`, `.ticker` rules (lines ~349-448).
- Read: `nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx` (verify skeleton structure matches loaded card).

- [ ] **Step 1: Read the current HeroLiveTheorem component to confirm skeleton/loaded card structure parity.**

Open `nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx`. Confirm:
- Skeleton (lines ~110-138) renders `.theorem-card` → `.theorem-card-head` → `.theorem-card-body` with a single `.theorem-statement` div and `.theorem-tag` div.
- Loaded card (lines ~141-162) renders the same three regions plus `.theorem-name`.

**Decision:** if the skeleton is missing a `.theorem-name` placeholder, add an empty placeholder div in the skeleton so heights match. If structures already match, skip.

- [ ] **Step 2: Modify `.theorem-statement` rule in `styles.css` to fix height with vertical centering and overflow clipping.**

Locate the rule starting at `.theorem-statement {` in `nasrudin-frontend/src/styles/styles.css` (around line 352). Replace the existing rule with:

```css
.theorem-statement {
  font-family: "STIX Two Math", "Cambria Math", "Source Serif 4", serif;
  font-size: clamp(16px, 2.4vw, 22px);
  line-height: 1.4;
  color: var(--ink-900);
  text-align: center;
  padding: 16px 12px;
  height: 140px;
  display: flex;
  align-items: center;
  justify-content: center;
  overflow: hidden;
  font-style: italic;
  font-weight: 400;
}
.theorem-statement > * {
  max-width: 100%;
  overflow: hidden;
  text-overflow: ellipsis;
}
```

Rationale: `height` (not `min-height`) prevents grow; `overflow: hidden` prevents push; `clamp()` font shrinks long LaTeX before clipping; flex centers vertically so short statements still look right.

- [ ] **Step 3: Add explicit `min-height` to `.ticker` so a missing line doesn't collapse the ticker box.**

Locate `.ticker {` rule (around line 414). Change `padding: 14px 18px;` to keep that, and add `min-height: 48px;` after the `position: relative;` line. The full updated rule:

```css
.ticker {
  margin-top: 16px;
  padding: 14px 18px;
  border: 1px dashed var(--paper-300);
  border-radius: var(--radius-md);
  background: var(--paper-50);
  display: flex;
  align-items: center;
  gap: 12px;
  font-size: 13px;
  color: var(--ink-700);
  overflow: hidden;
  position: relative;
  min-height: 48px;
}
```

- [ ] **Step 4: Stabilize `.theorem-card-body` padding so left/right column rotations don't shift.**

The existing rule (around line 349) is `padding: 28px 24px 8px;`. Keep desktop value but ensure stable. No change at this step — confirm visually in Step 5 that nothing wobbles.

- [ ] **Step 5: Start dev server and visually verify the card doesn't shift through 3 rotations.**

Run: `just dev-frontend` (or `cd nasrudin-frontend && pnpm dev`). Open `http://localhost:3000/` in a browser at 1024px width. Wait for the live card to load a real theorem. Watch through 3 rotations (~17 seconds).

**Expected:** the card's outer dimensions stay identical; only the inner statement text changes. The `.hero-quote` block and `.hero-meta` stats below it on the left column do not move.

If shift is still visible: check `.theorem-card-head` for variable content (the `verified-badge` text "Verified · Lean 4" is fixed, so should be stable) and re-verify `.theorem-statement` rule applied (open devtools, inspect element).

- [ ] **Step 6: Verify on mobile width (375px).**

Resize browser to 375px. The hero stacks (text → card). Watch 3 rotations. Confirm the section below (the "How it works" `§ 01 / 06` block) does not shift up/down on rotation.

If KaTeX block math is still pushing height: open devtools, find `.theorem-statement > .katex-display` (KaTeX block class) and confirm it inherits the `overflow: hidden` and `max-width: 100%`. If not, add a more specific rule:

```css
.theorem-statement .katex-display,
.theorem-statement .katex {
  max-width: 100%;
  overflow: hidden;
  margin: 0;
}
```

Add this immediately after the `.theorem-statement > *` rule.

- [ ] **Step 7: Commit.**

```bash
git add nasrudin-frontend/src/styles/styles.css nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx
git commit -m "frontend: stabilize live theorem card height — no rotation reflow"
```

(Drop the `HeroLiveTheorem.tsx` from the add list if Step 1 didn't modify it.)

---

## Task 2: Landing-page mobile pass — add `≤480` breakpoint, tighten `≤640`

**Goal:** Landing page (`/`) is legible and uncramped at 360 / 480 / 640 widths. Nothing overflows horizontally. Hero/section padding, font sizes, and the live theorem card all shrink proportionally.

**Files:**
- Modify: `nasrudin-frontend/src/styles/styles.css` — extend the `@media (max-width: 640px)` block, add new `@media (max-width: 480px)` block.

- [ ] **Step 1: Locate the existing `@media (max-width: 640px)` block in `styles.css` (around line 1209) and expand it.**

Replace the existing `@media (max-width: 640px)` block with:

```css
@media (max-width: 640px) {
  .container, .container-wide { padding: 0 var(--space-5); }
  .nav { display: none; }
  .nav-cta { display: inline-flex; }      /* keep CTA visible */
  .topbar-inner { padding: 12px var(--space-5); }
  .brand-tag { display: none; }            /* hide subtitle on phones */
  .brand { font-size: 20px; }

  .hero { padding: 48px 0 32px; }
  .hero-eyebrow { font-size: 11px; padding: 5px 12px 5px 8px; margin-bottom: 20px; }
  .hero-title { font-size: clamp(40px, 9vw, 56px); }
  .hero-sub { font-size: 18px; margin-top: 18px; }
  .hero-quote { margin-top: 28px; padding: 16px 0 16px 18px; }
  .hero-quote-text { font-size: 20px; }
  .hero-ctas { gap: 10px; margin-top: 28px; }
  .hero-ctas .btn { width: 100%; justify-content: center; }
  .hero-meta { margin-top: 36px; padding-top: 20px; gap: 18px; }
  .hero-meta-num { font-size: 24px; }

  .section { padding: 56px 0; }
  .section.compact { padding: 40px 0; }
  .section-head { margin-bottom: 28px; }
  .section-title { font-size: 28px; }
  .section-lede { font-size: 15px; margin-top: 12px; }

  .rediscover-grid { grid-template-columns: 1fr; }
  .browser-row { grid-template-columns: 80px 1fr 24px; }
  .browser-row > :nth-child(3),
  .browser-row > :nth-child(4),
  .browser-row > :nth-child(5),
  .browser-row.head > :nth-child(3),
  .browser-row.head > :nth-child(4),
  .browser-row.head > :nth-child(5) { display: none; }
  .browser-detail { grid-template-columns: 1fr; }
  .pipe-row { grid-template-columns: 1fr; gap: 12px; }
  .section-head { grid-template-columns: 1fr; gap: 16px; }
  .section-num { padding: 0 0 12px; border-right: none; border-bottom: 1px solid var(--paper-300); }

  .theorem-statement { height: 120px; padding: 12px 8px; }
  .theorem-card-body { padding: 20px 18px 8px; }
  .theorem-card-head { padding: 12px 16px; }
  .ticker { padding: 12px 14px; min-height: 44px; }

  .install-cli-body { padding: 18px; font-size: 12px; }
}
```

- [ ] **Step 2: Add a new `@media (max-width: 480px)` block immediately after the 640 block.**

```css
@media (max-width: 480px) {
  .container, .container-wide { padding: 0 16px; }
  .topbar-inner { padding: 10px 16px; }

  .hero { padding: 32px 0 24px; }
  .hero-title { font-size: clamp(32px, 9vw, 44px); }
  .hero-sub { font-size: 16px; }
  .hero-quote-text { font-size: 18px; }
  .hero-meta { gap: 14px; }
  .hero-meta-num { font-size: 22px; }
  .hero-meta-label { font-size: 11px; }

  .section { padding: 40px 0; }
  .section.compact { padding: 32px 0; }
  .section-title { font-size: 24px; }

  .theorem-statement { height: 100px; font-size: clamp(14px, 4vw, 18px); }
  .theorem-card-body { padding: 16px 14px 8px; }
  .theorem-card-head { padding: 10px 14px; }
  .theorem-name { font-size: 16px; }
  .theorem-tag { font-size: 11px; }
  .ticker { padding: 10px 12px; font-size: 12px; min-height: 40px; }
  .ticker-text { font-size: 11.5px; }

  .nav-cta { padding: 6px 12px; font-size: 13px; }

  .footer { padding: 48px 0 32px; }
  .footer-grid { grid-template-columns: 1fr; gap: 32px; margin-bottom: 32px; }
  .footer-brand { font-size: 26px; }
  .footer-tag { font-size: 18px; }
  .footer-bottom { flex-direction: column; gap: 8px; }
}
```

- [ ] **Step 3: Verify at 360, 480, 640 widths.**

With `pnpm dev` running, open `http://localhost:3000/` and resize browser through:
- **360px** — confirm no horizontal scroll, hero title fits without overflow, live card fits, footer columns stack.
- **480px** — same checks plus rediscovery cards single-column, pipeline rows stack.
- **640px** — CTA button visible in topbar, "Synthetic theorem · Lean 4" subtitle hidden, hero buttons full-width.

If any element overflows: identify in devtools (toggle outline `* { outline: 1px solid red; }`) and add the offending rule to the appropriate breakpoint block.

- [ ] **Step 4: Commit.**

```bash
git add nasrudin-frontend/src/styles/styles.css
git commit -m "frontend: tighten landing mobile layout — 480 breakpoint, kinder 640 rules"
```

---

## Task 3: Fix `.app-header-inner` stacking and add app-shell mobile rules

**Goal:** The platform app header (used on all `/browse`, `/library`, etc. routes) lays out as brand-left, actions-right at all widths instead of stacking vertically at ≤1024.

**Files:**
- Modify: `nasrudin-frontend/src/styles/platform.css` — `.app-header-inner` and add new mobile rules.

- [ ] **Step 1: Locate and replace the broken 1024 rule for `.app-header-inner`.**

In `nasrudin-frontend/src/styles/platform.css`, find the `@media (max-width: 1024px)` block (around line 1373). The existing line `.app-header-inner { grid-template-columns: 1fr; }` causes vertical stacking. Replace it with:

```css
  .app-header-inner { grid-template-columns: auto auto; gap: 12px; }
```

Keep the existing `.app-search { display: none; }` line right after — search is hidden at this breakpoint.

- [ ] **Step 2: Add a `≤640` block for `platform.css` (it currently has none).**

After the closing `}` of the `@media (max-width: 1024px)` block, add:

```css
@media (max-width: 640px) {
  .app-header-inner { padding: 10px var(--space-5); }
  .app-actions { gap: 12px; }
  .app-nav-link { display: none; }       /* avatar + CTA only */
  .app-subnav-inner { padding: 0 var(--space-5); gap: 20px; }
  .page-head { padding: 32px 0 24px; }
  .page-head h1 { font-size: 32px; }
  .page-head .lede { font-size: 15px; }
  .page-body { padding: 28px 0 56px; }
  .crumbs { font-size: 11px; gap: 6px; }
}
```

- [ ] **Step 3: Add a `≤480` block for `platform.css` immediately after.**

```css
@media (max-width: 480px) {
  .app-header-inner { padding: 8px 16px; }
  .app-brand { font-size: 17px; }
  .page-head { padding: 24px 0 16px; }
  .page-head h1 { font-size: 26px; }
  .page-head .lede { font-size: 14px; }
  .page-body { padding: 20px 0 40px; }
  .card { padding: 16px; }
  .card-elevated { padding: 16px; }
}
```

- [ ] **Step 4: Verify by visiting any platform route at 1024 / 640 / 480.**

With dev server running, open `http://localhost:3000/browse` (any logged-out-friendly route works). Resize:
- **1024**: brand left, avatar/CTA right, single row.
- **640**: same — brand left, actions right, no vertical stack.
- **480**: same, smaller.

- [ ] **Step 5: Commit.**

```bash
git add nasrudin-frontend/src/styles/platform.css
git commit -m "frontend: app shell mobile — fix header stack, add 640/480 rules"
```

---

## Task 4: `/browse` route mobile audit

**Goal:** `/browse` is usable at 360/480/640, with table rows collapsing properly and the search header not overflowing.

**Files:**
- Read: `nasrudin-frontend/src/routes/browse.tsx`, `nasrudin-frontend/src/components/browse/ResultCard.tsx`.
- Modify: `nasrudin-frontend/src/styles/platform.css` and/or `styles.css` if browse-specific rules need tightening.

- [ ] **Step 1: Read the browse route component.**

Read `nasrudin-frontend/src/routes/browse.tsx` and `nasrudin-frontend/src/components/browse/ResultCard.tsx`. Note class names used. Most browse styles are in `styles.css` under `/* THEOREM BROWSER */` (around line 797).

- [ ] **Step 2: Visit `/browse` at 360, 480, 640.**

Run dev server. Open `http://localhost:3000/browse`. At each width, check:
- `.browser-head` (search + filter chips): does it wrap reasonably?
- `.browser-row`: at 640 the existing rule already collapses to 3 cols — confirm working.
- `.browser-detail`: at 640 the existing rule collapses to 1 col — confirm working.
- Filter chips: do they wrap? They have `flex-wrap: wrap` already.

- [ ] **Step 3: Patch any issues found.**

Likely fixes (apply only if issue observed):
- `.browser-search` may not shrink: add `width: 100%; max-width: none` inside `@media (max-width: 640px)`.
- `.browser-row` ID column at 80px may still crowd at 360: in the new `@media (max-width: 480px)` block add `.browser-row { grid-template-columns: 64px 1fr 20px; gap: 10px; padding: 12px 16px; }`.
- `.browser-stmt` font 16px italic may overflow on narrow phones: add `font-size: 14px` to the 480 block.

Add fixes to the existing `@media (max-width: 640px)` block in `styles.css`, or to the new `@media (max-width: 480px)` block.

- [ ] **Step 4: Commit (only if changes were made).**

```bash
git add nasrudin-frontend/src/styles/styles.css
git commit -m "frontend: /browse mobile polish at 480px"
```

If no changes were needed, skip the commit and note in your task completion that no fixes were required.

---

## Task 5: `/library` route mobile audit

**Files:**
- Read: `nasrudin-frontend/src/routes/library.tsx`.
- Modify: `nasrudin-frontend/src/styles/platform.css` and/or `styles.css` as needed.

- [ ] **Step 1: Read the library route.**

Read `nasrudin-frontend/src/routes/library.tsx`. Note its CSS class names. Many library pages use `.card` + custom grids — observe what's used.

- [ ] **Step 2: Visit `/library` at 360, 480, 640, 1024.**

For each width, identify:
- Does any container overflow horizontally?
- Are grids appropriate (stack at 640, 1 col at 480)?
- Are fonts/buttons cramped?

- [ ] **Step 3: Patch issues by adding rules to existing breakpoint blocks in `platform.css` or to a new section if library-specific styles exist.**

If `/library` uses inline styles or component-scoped CSS rather than the shared sheet, pencil any necessary fixes into the JSX directly via `style={{}}` or className changes guarded by Tailwind/utility classes — but per the spec we prefer CSS file edits. Document the fix at the appropriate breakpoint block.

- [ ] **Step 4: Commit (only if changes were made).**

```bash
git add nasrudin-frontend/src/styles/platform.css nasrudin-frontend/src/styles/styles.css nasrudin-frontend/src/routes/library.tsx
git commit -m "frontend: /library mobile polish"
```

(Adjust the `git add` to match files actually changed.)

---

## Task 6: `/search` and `/search/concept` routes mobile audit

**Goal:** Search page facet sidebar collapses sensibly on mobile; form-builder (concept search) usable at 480.

**Files:**
- Read: `nasrudin-frontend/src/routes/search.tsx`, `nasrudin-frontend/src/routes/search.concept.tsx`, `nasrudin-frontend/src/components/search/*.tsx`.
- Modify: `nasrudin-frontend/src/styles/platform.css` (`.search-layout`, `.facet-*`, `.result-*` rules, lines ~411-521).

- [ ] **Step 1: Read both route files and the search components.**

```bash
ls nasrudin-frontend/src/components/search/
```

Read each `.tsx` in that directory. Note class names — `.facet-list`, `.facet-group`, `.search-results-bar`, `.result-card`, plus any from `FormBuilder.tsx` for the concept search.

- [ ] **Step 2: Visit `/search` at all four widths.**

The existing `@media (max-width: 1024px)` already collapses `.search-layout` to 1 col. Confirm:
- Facet sidebar appears above results at ≤1024.
- At 640 the facet groups don't sprawl unreasonably.
- At 480 confirm no horizontal scroll.

- [ ] **Step 3: Add facets-collapsible behavior at ≤640 via `<details>` / CSS only.**

Decision per spec: if the `/search` page renders many facets visible all at once, the facets sidebar at 1024 collapsing to a stack above results consumes a lot of vertical space. Mitigation: at ≤640, wrap each `.facet-group` in a CSS `display: none` toggle controlled by a `<details>` element if the JSX supports it, otherwise leave as-is and add the rule:

```css
@media (max-width: 640px) {
  .search-layout { gap: 20px; }
  .facet-group { margin-bottom: 16px; }
  .facet-group h5 { margin-bottom: 8px; }
  .facet-list li { padding: 4px 8px; font-size: 12.5px; }
}
```

Add to the existing 640 block in `platform.css`.

- [ ] **Step 4: Visit `/search/concept` at all four widths.**

Inspect `FormBuilder.tsx` rendering. Likely uses form fields — check that inputs are full-width on mobile and don't overflow. Add to `platform.css`:

```css
@media (max-width: 640px) {
  .search-layout input,
  .search-layout select,
  .search-layout textarea { width: 100%; }
}
```

(Add only if input overflow is observed.)

- [ ] **Step 5: Verify result-cards.**

`.result-card` is a 2-col grid (`1fr auto`). On narrow phones the right side (verified-badge + meta) may crowd. If observed, add to the 480 block:

```css
@media (max-width: 480px) {
  .result-card { grid-template-columns: 1fr; gap: 8px; }
  .result-side { text-align: left; }
  .result-stmt { font-size: 18px; }
}
```

- [ ] **Step 6: Commit.**

```bash
git add nasrudin-frontend/src/styles/platform.css
git commit -m "frontend: /search and /search/concept mobile polish"
```

---

## Task 7: `/workers` route mobile audit

**Files:**
- Read: `nasrudin-frontend/src/routes/workers.tsx`.

- [ ] **Step 1: Read the route.**

Read `nasrudin-frontend/src/routes/workers.tsx`. Note class names — likely uses `.card`, `.worker-list`, or a custom worker table.

- [ ] **Step 2: Visit `/workers` at 360, 480, 640, 1024.**

Identify overflow and crowding. Worker tables are typically the worst offender — check if a horizontal scroll wrapper or column-hiding strategy is needed.

- [ ] **Step 3: Apply fixes.**

Common patterns:
- Wrap any `<table>` in `<div style={{ overflowX: 'auto' }}>` (in JSX) or wrap with `.table-scroll { overflow-x: auto; }` in CSS.
- For worker-list grids similar to `.worker-list li` in `styles.css`, add a 480 rule that drops the rate column or shrinks fonts.

- [ ] **Step 4: Commit if changes made.**

```bash
git add nasrudin-frontend/src/styles/platform.css nasrudin-frontend/src/routes/workers.tsx
git commit -m "frontend: /workers mobile polish"
```

---

## Task 8: `/api-keys` route mobile audit

**Files:**
- Read: `nasrudin-frontend/src/routes/api-keys.tsx`, `nasrudin-frontend/src/components/apikeys/*.tsx`.

- [ ] **Step 1: Read the route and components.**

```bash
ls nasrudin-frontend/src/components/apikeys/
```

Read `nasrudin-frontend/src/routes/api-keys.tsx` and each component file. Note class names.

- [ ] **Step 2: Visit `/api-keys` at all four widths.**

API key tables are typically wide (name, prefix, created, last-used, actions). Check for overflow.

- [ ] **Step 3: Apply fixes.**

Likely fix: hide the "last used" or "created" column at ≤640, and at ≤480 stack each row as a card. Specific approach depends on what the route renders — pick the simplest CSS-only fix.

If the page uses `.lead-table`-style HTML table classes, wrap in scrolling container. If it uses CSS grid rows, hide non-essential columns at narrow widths.

- [ ] **Step 4: Verify the `CreateKeyDialog` modal at 360.**

Open the create-key flow. Confirm the dialog fits and doesn't overflow horizontally. If using a portal/modal class, ensure `max-width: 90vw` and `padding: 16px` at ≤480.

- [ ] **Step 5: Commit.**

```bash
git add nasrudin-frontend/src/styles/platform.css nasrudin-frontend/src/components/apikeys/
git commit -m "frontend: /api-keys mobile polish"
```

---

## Task 9: `/theorem/$id` mobile polish

**Goal:** The big statement block doesn't overflow at 360. Side panel stacks below main content at ≤1024 (already does — verify).

**Files:**
- Read: `nasrudin-frontend/src/routes/theorem.$id.tsx`, `nasrudin-frontend/src/components/theorem/*.tsx`.
- Modify: `nasrudin-frontend/src/styles/platform.css` — `.thm-*` rules.

- [ ] **Step 1: Visit `/theorem/<some-id>` at 360, 480, 640, 1024.**

Pick any theorem ID from `/browse` to navigate. Inspect:
- `.thm-name` (56px font) — overflows at 360?
- `.thm-statement-big` (38px italic STIX) — overflows?
- `.thm-statement-block` padding (48px 32px) — too much on phones?
- `.thm-proof-pre` already has `overflow-x: auto` — good.
- Side panel at ≤1024 stacks below main — confirm.

- [ ] **Step 2: Add 640 rules.**

In the existing `@media (max-width: 640px)` block in `platform.css` (add after Task 3's additions), include:

```css
  .thm-page { gap: 28px; }
  .thm-name { font-size: clamp(32px, 8vw, 44px); }
  .thm-statement-block { padding: 32px 20px; margin-bottom: 24px; }
  .thm-statement-big { font-size: clamp(22px, 6vw, 32px); }
  .thm-section { margin-top: 32px; }
  .thm-section h3 { font-size: 20px; }
  .thm-actions { gap: 8px; }
  .thm-actions .btn { flex: 1 1 auto; min-width: 0; }
  .uses-grid { grid-template-columns: 1fr; }
  .lineage li { grid-template-columns: 24px 1fr; gap: 12px; }
```

- [ ] **Step 3: Add 480 rules.**

In the new `@media (max-width: 480px)` block, append:

```css
  .thm-name { font-size: clamp(26px, 9vw, 36px); }
  .thm-statement-block { padding: 24px 14px; }
  .thm-statement-big { font-size: clamp(18px, 6.5vw, 26px); }
  .thm-proof-pre { padding: 16px 14px; font-size: 12px; }
  .thm-side .meta-list li { font-size: 12px; gap: 8px; }
```

- [ ] **Step 4: Verify and commit.**

```bash
git add nasrudin-frontend/src/styles/platform.css
git commit -m "frontend: /theorem/$id mobile polish"
```

---

## Task 10: `/profile` mobile fix (currently broken)

**Goal:** Profile head doesn't visually break — avatar above name above tier-pill at ≤640.

**Files:**
- Modify: `nasrudin-frontend/src/styles/platform.css` — `.profile-*`, `.stat-*`, `.targeted-search-card` rules (lines ~526-718).

- [ ] **Step 1: Visit `/profile` at all four widths.**

Confirm the spec's claim: `.profile-head` is a 3-col grid (`auto 1fr auto`) with no mobile rule. At 640 it tries to fit avatar (96×96), name+bio, and tier-pill in one row → overflow.

- [ ] **Step 2: Add profile-head stacking at 640 to the existing block in `platform.css`.**

Append to the `@media (max-width: 640px)` block:

```css
  .profile-head {
    grid-template-columns: 64px 1fr;
    gap: 16px;
    padding: 32px 0 20px;
  }
  .profile-avatar { width: 64px; height: 64px; font-size: 28px; }
  .profile-name { font-size: 28px; }
  .profile-bio { font-size: 14px; }
  .profile-tier {
    grid-column: 1 / -1;
    text-align: left;
  }
  .stat-row { grid-template-columns: repeat(2, 1fr); margin: 24px 0; }
  .stat-cell { padding: 18px; }
  .stat-cell .num { font-size: 28px; }
  .saved-list li { grid-template-columns: 1fr auto; gap: 8px; }
  .saved-date { display: none; }
  .activity-feed li { grid-template-columns: 1fr; gap: 4px; }
  .targeted-search-card { grid-template-columns: 1fr; padding: 20px; gap: 16px; }
```

- [ ] **Step 3: Add 480 polish.**

Append to the `@media (max-width: 480px)` block:

```css
  .profile-name { font-size: 24px; }
  .profile-handle { font-size: 12px; }
  .stat-cell { padding: 14px; }
  .stat-cell .num { font-size: 24px; }
  .stat-cell .label { font-size: 10px; }
```

- [ ] **Step 4: Verify and commit.**

```bash
git add nasrudin-frontend/src/styles/platform.css
git commit -m "frontend: /profile mobile — stack head, shrink stat row"
```

---

## Task 11: `/pricing` mobile fix (tier cards never collapse to 1 col)

**Files:**
- Modify: `nasrudin-frontend/src/styles/platform.css` — `.tier-*`, `.targeted-band`, `.faq-*`, `.pricing-hero` rules (lines ~720-945).

- [ ] **Step 1: Visit `/pricing` at all four widths.**

Confirm cards are 2-up at ≤1024 (existing) but never go to 1-up — at 480, cards become too narrow.

- [ ] **Step 2: Add tier collapse and pricing polish to the 640 block.**

Append to `@media (max-width: 640px)`:

```css
  .pricing-hero { padding: 40px 0 20px; }
  .pricing-hero h1 { font-size: clamp(32px, 9vw, 44px); }
  .pricing-hero .lede { font-size: 16px; }
  .tier-grid { grid-template-columns: 1fr; gap: 16px; margin: 32px 0 24px; }
  .tier { padding: 24px 20px; }
  .tier-name { font-size: 20px; }
  .tier-price-num { font-size: 40px; }
  .targeted-band {
    grid-template-columns: 1fr;
    gap: 24px;
    padding: 28px 20px;
    margin: 40px 0;
  }
  .targeted-band h2 { font-size: 26px; }
  .targeted-band p { font-size: 15px; }
  .donate-quote { font-size: 24px; }
  .faq-grid { grid-template-columns: 1fr; gap: 24px; }
  .donate-band { padding: 40px 0; }
```

- [ ] **Step 3: Append 480 polish.**

```css
  .pricing-hero h1 { font-size: clamp(26px, 9vw, 36px); }
  .tier { padding: 20px 16px; }
  .tier-features li { font-size: 13px; }
  .targeted-band h2 { font-size: 22px; }
  .donate-quote { font-size: 20px; }
```

Append into the existing `@media (max-width: 480px)` block.

- [ ] **Step 4: Verify and commit.**

```bash
git add nasrudin-frontend/src/styles/platform.css
git commit -m "frontend: /pricing mobile — tiers stack, shrink hero+FAQ"
```

---

## Task 12: `/leaderboard` mobile fix

**Files:**
- Read: `nasrudin-frontend/src/routes/leaderboard.tsx`.
- Modify: `nasrudin-frontend/src/styles/platform.css` — `.lead-*` rules.

- [ ] **Step 1: Visit `/leaderboard` at all four widths.**

`.lead-podium` already collapses at ≤1024. The `.lead-table` does not — it's a wide 4-col table. At 480, columns crush.

- [ ] **Step 2: Wrap the table in a horizontal-scroll container if not already.**

Read `nasrudin-frontend/src/routes/leaderboard.tsx`. Find where the `<table className="lead-table">` is rendered. Wrap it:

```tsx
<div className="lead-table-scroll">
  <table className="lead-table">
    {/* ... */}
  </table>
</div>
```

Then add to `platform.css` (top-level, not in a media query):

```css
.lead-table-scroll {
  overflow-x: auto;
  margin: 0 calc(-1 * var(--space-8));
  padding: 0 var(--space-8);
  -webkit-overflow-scrolling: touch;
}
.lead-table-scroll .lead-table { min-width: 560px; }
```

The negative margin lets the scroll container break out of the page padding so users can swipe edge-to-edge.

- [ ] **Step 3: Polish the podium and tabs at 640/480.**

Add to the `@media (max-width: 640px)` block:

```css
  .lead-step { padding: 20px 14px; }
  .lead-rank { font-size: 28px; }
  .lead-handle { font-size: 18px; }
  .lead-tabs { flex-wrap: wrap; }
  .lead-tab { font-size: 12px; padding: 6px 12px; }
```

Add to the `@media (max-width: 480px)` block:

```css
  .lead-step { padding: 16px 10px; }
  .lead-handle { font-size: 16px; }
  .lead-num { font-size: 12px; }
```

- [ ] **Step 4: Commit.**

```bash
git add nasrudin-frontend/src/styles/platform.css nasrudin-frontend/src/routes/leaderboard.tsx
git commit -m "frontend: /leaderboard mobile — scroll table, shrink podium"
```

---

## Task 13: `/api-docs` mobile audit

**Files:**
- Read: `nasrudin-frontend/src/routes/api-docs.tsx`.
- Modify: `nasrudin-frontend/src/styles/platform.css` — `.api-*`, `.endpoint-*`, `.code-*` rules.

- [ ] **Step 1: Visit `/api-docs` at all four widths.**

`.api-grid` collapses to 1 col at ≤1024. `.api-toc` becomes a horizontal-ish list. Check:
- Long endpoint paths in `.endpoint-head` overflow?
- Code blocks already `overflow-x: auto` — good.

- [ ] **Step 2: Add 640 polish.**

Append to the 640 block:

```css
  .api-hero { padding: 36px 0 16px; }
  .api-grid { gap: 28px; }
  .api-toc { padding-left: 12px; }
  .api-toc a { font-size: 12px; }
  .endpoint { margin-bottom: 40px; }
  .endpoint-head {
    flex-wrap: wrap;
    padding: 12px 14px;
    font-size: 13px;
  }
  .endpoint-tier { margin-left: 0; width: 100%; margin-top: 4px; }
  .endpoint h3 { font-size: 20px; }
  .code-block { padding: 14px 16px; font-size: 11.5px; }
  .code-tabs { flex-wrap: wrap; }
```

- [ ] **Step 3: Add 480 polish.**

```css
  .endpoint h3 { font-size: 18px; }
  .endpoint .desc { font-size: 13px; }
  .code-block { padding: 12px 14px; font-size: 11px; }
```

Append to 480 block.

- [ ] **Step 4: Commit.**

```bash
git add nasrudin-frontend/src/styles/platform.css
git commit -m "frontend: /api-docs mobile polish"
```

---

## Task 14: `/signin` mobile fix (auth-side hidden on small phones)

**Files:**
- Modify: `nasrudin-frontend/src/styles/platform.css` — `.auth-*` rules (lines ~1170-1370).

- [ ] **Step 1: Visit `/signin` at all four widths.**

The `@media (max-width: 1024px)` rule already stacks `.auth-page` to 1 col with the dark `.auth-side` becoming a 320px-min header. That uses a lot of vertical space on phones.

- [ ] **Step 2: Hide `.auth-side` entirely at ≤640 (form-only experience on phones).**

Append to the 640 block:

```css
  .auth-page { grid-template-columns: 1fr; }
  .auth-side { display: none; }
  .auth-form-wrap { padding: 32px 20px; max-width: 100%; }
  .auth-form-wrap h1 { font-size: 28px; }
  .auth-form-wrap .lede { font-size: 14px; margin-bottom: 24px; }
  .field input { font-size: 16px; }   /* prevents iOS zoom on focus */
  .oauth-grid { grid-template-columns: 1fr; }
  .auth-tabs { margin-bottom: 24px; }
```

- [ ] **Step 3: Add 480 polish.**

Append to 480 block:

```css
  .auth-form-wrap { padding: 24px 16px; }
  .auth-form-wrap h1 { font-size: 24px; }
  .auth-tab { font-size: 13px; margin-right: 20px; }
```

- [ ] **Step 4: Verify by visiting `/signin` at 360 and 480 — confirm no horizontal scroll, form is comfortable.**

- [ ] **Step 5: Commit.**

```bash
git add nasrudin-frontend/src/styles/platform.css
git commit -m "frontend: /signin mobile — hide auth-side, prevent iOS zoom"
```

---

## Task 15: Remaining route audit — `/jobs`, `/conjecture`, `/conjecture/$id`, `/research`, `/research/$id`, `/sponsor`, `/settings`

**Goal:** Each remaining route inspected at four widths, fixes applied as needed.

**Files:** read each route + components, modify `platform.css` / `styles.css` per findings.

This task is intentionally one umbrella so a single subagent can do the audit-fix pass without ping-ponging. Document fixes per route in the commit message.

- [ ] **Step 1: For each route below, read the file, visit at 360/480/640/1024, and patch issues.**

Routes:
- `nasrudin-frontend/src/routes/jobs.tsx`
- `nasrudin-frontend/src/routes/conjecture.tsx`
- `nasrudin-frontend/src/routes/conjecture.$id.tsx` (+ `nasrudin-frontend/src/components/conjecture/JobProgress.tsx`)
- `nasrudin-frontend/src/routes/research.tsx`
- `nasrudin-frontend/src/routes/research.$id.tsx`
- `nasrudin-frontend/src/routes/sponsor.tsx`
- `nasrudin-frontend/src/routes/settings.tsx` (+ `nasrudin-frontend/src/components/settings/*.tsx`)

For each: identify any horizontal overflow, font sizes that don't fit, grids that don't collapse. Apply fixes to the existing 640 / 480 blocks in `platform.css` (or add a route-specific section if rules are unique). Stay consistent with the patterns established in Tasks 9-14.

- [ ] **Step 2: Common patterns to apply by default to any newly-touched route.**

If a route has tables that don't fit: wrap in `.lead-table-scroll` (defined in Task 12) — if scroll isn't appropriate, hide non-essential columns at the right breakpoint.

If a route has multi-column grids: collapse to 1 col at 640 unless an obvious 2-col layout still works on phones.

If inputs exist anywhere: ensure `font-size: 16px` minimum at ≤640 to prevent iOS zoom-on-focus.

If `.card` items exist: rely on Task 3's app-shell rule (card padding 16px at ≤480).

- [ ] **Step 3: Commit one consolidated commit at the end.**

```bash
git add nasrudin-frontend/src/styles/platform.css nasrudin-frontend/src/styles/styles.css nasrudin-frontend/src/routes/ nasrudin-frontend/src/components/
git commit -m "frontend: mobile polish remaining routes (jobs/conjecture/research/sponsor/settings)"
```

If no changes were needed for a given route, note that in the commit body.

---

## Task 16: Final full-site verification pass

**Goal:** Walk every route at 360, 480, 640, 1024 and confirm zero issues remain.

- [ ] **Step 1: Confirm dev server is running.**

```bash
just dev-frontend
```

If not running, start it. Wait for "Local: http://localhost:3000" in the output.

- [ ] **Step 2: At width 360, visit each route and check for issues.**

Routes (visit in order, takes ~10 minutes total):

```
/
/browse
/library
/search
/search/concept
/conjecture
/conjecture/<existing-id>     # pick one from /jobs or skip if none
/research
/research/<existing-id>       # ditto
/theorem/<existing-id>        # pick one from /browse
/profile
/leaderboard
/pricing
/api-docs
/api-keys
/workers
/jobs
/sponsor
/settings
/signin
```

For each: confirm no horizontal scroll on the page (page-level `overflow-x: hidden` is set on `.page`/`.app`, but content shouldn't be forcing any), no obviously-cramped buttons or cut-off text, all primary CTAs reachable.

- [ ] **Step 3: Repeat at 480, 640, 1024.**

Same routes. Quicker (most issues caught at 360).

- [ ] **Step 4: Layout-shift smoke test on `/`.**

At 1024 width: open `/`, observe the live theorem card cycle through 3 rotations. Confirm zero pixel movement of the surrounding content.

At 375 width: same test — confirm no movement of the section below.

If any shift remains: revisit Task 1 logic — likely `.theorem-card-head` content varying or KaTeX overflowing the explicit height set on `.theorem-statement`.

- [ ] **Step 5: Run frontend type/lint check.**

```bash
cd nasrudin-frontend && pnpm check
```

Expected: passes with no errors. CSS-only changes shouldn't impact TS, but if any JSX touches in Tasks 1, 7, 8, 12, 15 broke types, fix them now.

- [ ] **Step 6: Build the frontend to confirm CSS doesn't trip the build.**

```bash
cd nasrudin-frontend && pnpm build
```

Expected: completes without error.

- [ ] **Step 7: Document anything skipped.**

If any route's audit was deferred (e.g., a complex page that needs design input), record it as a follow-up in the commit message of the next/final commit.

- [ ] **Step 8: No final commit unless fixes were applied.**

If Steps 1-7 surfaced real issues, fix them and commit:

```bash
git add nasrudin-frontend/
git commit -m "frontend: final mobile sweep — fix remaining issues found in walkthrough"
```

If Steps 1-7 were clean, no commit; the work is done.
