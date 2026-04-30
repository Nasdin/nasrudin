# Frontend mobile responsiveness + live theorem layout-shift fix

**Date:** 2026-04-30
**Status:** spec

## Problem

Two related issues on `nasrudin-frontend`:

1. **Layout shift on landing.** `HeroLiveTheorem` rotates between real verified theorems every 5.5s. Each theorem has a different KaTeX-rendered statement, so the card's height changes on every rotation. On viewports ≤1024px the hero stacks (text → card), so the card's growing/shrinking pushes everything below it. Even on desktop the card itself reflows visibly. Result: the "left section" content jumps every few seconds, hostile to reading.

2. **Mobile responsiveness gaps across the site.** The two existing breakpoints (1024 / 640) cover the worst-case grids but leave gaps:
   - Hero/section padding doesn't scale (80px / 96px stays put on phones).
   - Several routes have no mobile rule at all (`/profile`, `/pricing` 1-col, app header).
   - No <480px breakpoint for narrow phones (360px–414px is the realistic floor).
   - The `.app-header-inner` collapses to a 1-column vertical stack at 1024 — visually broken on tablets.

## Goals

- Zero layout shift in the live-theorem card and its surroundings during normal rotation.
- All existing routes legible and usable at 360 / 480 / 640 / 1024 / wider widths.
- No visual redesign — preserve current typography, color, and component identity. This is a sizing/layout pass.
- CSS-only where possible. JSX touch-ups in `HeroLiveTheorem.tsx` only if needed for stable structure.

## Non-Goals

- Touch-specific UX (swipe, pull-to-refresh).
- Dark-mode mobile-specific tweaks.
- New components — no hamburger menu, no mobile-only chrome.
- Backend or data-layer changes.

## Architecture

CSS-only changes in two files:

- `nasrudin-frontend/src/styles/styles.css` — landing page + theorem card + ticker.
- `nasrudin-frontend/src/styles/platform.css` — app shell + all platform routes.

Possible small JSX changes in `nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx` only if the skeleton's outer structure needs to mirror the loaded card more precisely.

### Breakpoint strategy

Three breakpoints, retaining the existing two and adding 480:

- `≤1024px` (existing) — multi-column grids collapse to single column.
- `≤640px` (existing) — tablet/landscape phone — tighter padding, simpler chrome, primary nav collapses.
- `≤480px` (new) — narrow phones — minimum sizes, single column everywhere, aggressive font shrinks, container padding 16px.

## Design

### §1 Layout-shift fix on `HeroLiveTheorem`

**Goal:** the card occupies the same total pixel height regardless of which theorem is showing or whether the skeleton is up.

**Changes to `.theorem-card` and inner regions in `styles.css`:**

- `.theorem-statement`
  - Replace `min-height: 70px` with a fixed `height` per breakpoint:
    - desktop / ≥640: `height: 140px`
    - ≤640: `height: 120px`
    - ≤480: `height: 100px`
  - Add `display: flex; align-items: center; justify-content: center; overflow: hidden`.
  - Statement font size becomes `clamp(16px, 2.4vw, 22px)` so long LaTeX shrinks before clipping.

- `.theorem-card-body`
  - Stable padding per breakpoint (28/24, 20/18, 16/14).
  - Keep `.theorem-name` and `.theorem-tag` always rendered when a theorem is present (already the case).

- `.ticker`
  - Already `white-space: nowrap; overflow: hidden`. Add explicit `min-height` matching one line of monospace at 12.5px (~32px including padding) so a missing line doesn't collapse the box.

- Skeleton state in `HeroLiveTheorem.tsx`
  - Confirm the skeleton renders the same outer card structure (head, body, no foot — matches loaded card). Currently it does. If a `theorem-tag` div is missing, add a placeholder so the body height matches.

**Result:** rotating the theorem cycles only inner content; outer dimensions never change. The hero text column (mobile or desktop) holds steady.

### §2 Landing-page mobile pass (`styles.css`)

| Element | ≤1024 (existing) | ≤640 (new/tighter) | ≤480 (new) |
|---|---|---|---|
| `.hero` padding | 80px 0 48px | 48px 0 32px | 32px 0 24px |
| `.hero-title` | clamp(48,6vw,84) | clamp keeps min 40px | min 32px |
| `.hero-sub` | 24px | 18px | 16px |
| `.hero-quote-text` | 26px | 20px | 18px |
| `.hero-meta` | 2 cols (existing) | 2 cols, num 24px | 2 cols, num 22px |
| `.hero-ctas` | flex-wrap (existing) | full-width buttons stacked | same |
| `.section` padding | 96px 0 | 56px 0 | 40px 0 |
| `.section-title` | 36px (at 1024) | 28px | 24px |
| `.container, .container-wide` | 32px | 20px (existing) | 16px |
| `.nav` | hidden (≤640 existing) | hidden | hidden |
| Right-rail margin-note | 360 max-width | shrink to 100% | same |

**Mobile nav:** keep just the `Run a worker →` CTA visible on ≤640 inside the topbar (currently entire `.nav` hides). Implement by exempting the `.nav-cta` from the hide rule.

**Other landing components requiring inspection (no spec changes pre-audit):**
- `RediscoveryGrid` — already adapts.
- `PipelineDiagram`, `GAViz` — visual diagrams; verify no horizontal overflow at 360.
- `WorkerMap` — leaflet/svg — confirm container shrinks; map should auto-fit.
- `TheoremBrowser` — table rows already collapse at 640; verify ID column doesn't crowd at 360.
- `RunWorker` — already adapts.

### §3 Platform-route audit (`platform.css`)

For each route, verify at 360 / 480 / 640 / 1024 widths via headless browser, fix issues found:

- **`/browse`** — `.browser-row` collapses at 640. Add 480 polish if ID column crowds.
- **`/library`** — read file during implementation, audit grid/list layouts.
- **`/search`** — `.search-layout` collapses to 1 col at 1024. Facet sidebar moves above results. Add disclosure/`<details>` if facets are long.
- **`/search/concept`** — same shell as `/search`. Form-builder may need single-column at 640.
- **`/workers`** — read file, audit. Worker tables likely the worst offender.
- **`/api-keys`** — read file, audit. Tables may need horizontal scroll wrapper or card-per-row layout at 480.
- **`/theorem/$id`** — `.thm-page` adapts at 1024. Add `clamp()` to `.thm-statement-big` (38px → ~24px floor) to prevent overflow at 360. `.thm-name` 56px also too big — clamp to 36px floor.
- **`/profile`** — `.profile-head` is a 3-col grid with NO mobile rule → broken. Add stack at 640: avatar above name above tier-pill. `.stat-row` 4-col → 2-col at 1024 (existing) → 2-col at 480 with smaller `.num`.
- **`/pricing`** — `.tier-grid` is 2 cols at 1024 but never goes to 1 col → cards too narrow at 480. Add 1-col rule at 640. `.pricing-hero h1` 56px → clamp 36px floor. `.targeted-band` already adapts. `.faq-grid` 2 cols → 1 col at 640.
- **`/leaderboard`** — `.lead-podium` collapses at 1024. `.lead-table` needs a horizontal scroll wrapper or column hiding at 480 (rank, handle, count visible; rest hidden).
- **`/api-docs`** — `.api-grid` collapses at 1024. `.code-block` already has `overflow-x: auto`. Verify `.endpoint-head` doesn't break with long path on mobile.
- **`/signin`** — `.auth-page` adapts at 1024. `.auth-form-wrap` padding 64px → 32px → 20px at 480. `.auth-side` should hide entirely at 640 (just show form).
- **`/jobs`, `/conjecture`, `/conjecture/$id`, `/research`, `/research/$id`, `/sponsor`, `/settings`** — read each, audit, adjust.

**App-header fix:** `.app-header-inner` currently goes `grid-template-columns: 1fr` at 1024 — meaning brand, search, actions all stack vertically. Replace with: at ≤1024 keep brand left, actions right (2-col), search hidden (already hidden). At ≤480, shrink brand-tag (`Synthetic theorem · Lean 4`) — hide the tag.

### §4 Testing approach

After each component fix, verify in headless browser via the `gstack` skill at four widths: 360, 480, 640, 1024.

**Layout-shift verification specifically:**
1. Open `/` at 1024 width and 375 width.
2. Wait for the live card to load a real theorem.
3. Watch 3 rotations (≥16s).
4. Confirm zero pixel movement of:
   - The text column (`.hero-grid > div:first-child`) on desktop.
   - The "How it works" section header on mobile.
5. Take before/after screenshots for the spec record.

**General mobile verification:**
- No horizontal scroll at 360 width on any route.
- All buttons hit 44×44 minimum tap target.
- All text legible (≥14px body, ≥16px inputs to prevent iOS zoom).
- Tables either collapse, scroll horizontally, or hide non-essential columns — never overflow silently.

## Implementation phases

1. **Layout-shift fix** — `HeroLiveTheorem` card sizing. Verify on `/` at 1024 + 375.
2. **Landing-page mobile pass** — add 480 breakpoint, tighten 640 rules in `styles.css`. Verify entire `/` route.
3. **App shell** — fix `.app-header-inner` 1024 stacking, hide brand-tag at 480 in `platform.css`.
4. **Platform routes batch A** — `/browse`, `/library`, `/search`, `/search/concept`, `/workers`, `/api-keys`.
5. **Platform routes batch B** — `/theorem/$id`, `/profile`, `/pricing`, `/leaderboard`, `/api-docs`, `/signin`.
6. **Platform routes batch C (remaining)** — `/jobs`, `/conjecture(/$id)`, `/research(/$id)`, `/sponsor`, `/settings`.
7. **Final pass** — full-site review at 360/480/640/1024 widths, fix lingering issues.

## Risk / open questions

- **KaTeX block clipping:** if a theorem statement renders larger than 140px, it gets clipped. Trade-off: stable layout vs full statement visibility. Mitigation: smaller font via `clamp()` plus a `Link` wraps the card → click takes user to full theorem page. Accept clipping as the cost of stability.
- **Search facet collapse:** moving facets above results on mobile may waste vertical space if there are many facets. Decision deferred to implementation: if more than ~6 facets visible, wrap in `<details>` collapsible.
- **Headless browser availability:** if `gstack` isn't reliable in this session, fall back to manual viewport resize via dev server + report what was checked.
