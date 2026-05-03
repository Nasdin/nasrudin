# Verification Badge + Public Visibility Filter

**Date:** 2026-05-03
**Status:** Draft
**Scope:** Presentation-layer change. No verification mechanism, trust model, cascade graph, or DB migration is altered.

---

## Problem

The frontend currently renders three "Verified" sub-states as visually similar badges:

- **Lake-verified** — server ran `lake build`; Lean kernel confirmed.
- **Worker-verified** — a worker claims it lake-built locally; server lake confirmation pending.
- **Chain-verified** — only the Rust rewrite-rule replay accepted the proof; **no Lean kernel has touched it anywhere**.

Two issues:

1. **Chain-verified rows are publicly browsable.** They surface in `/browse`, `/discoveries`, public theorem detail pages, and the seed exporter — except seed export, which already filters them out (`handlers/seed.rs:312-316`). A casual visitor cannot tell that a "Chain-verified" theorem has zero kernel backing. We do not trust these and do not want to publish them.
2. **The badge wording overstates what `lake_build` is.** Internally the project uses "lake" (the Lean build tool) interchangeably with Lean kernel verification. To users, "Lake-verified" and "Worker-verified" sound like two unrelated pipelines rather than two locations where the same Lean kernel ran. The user-facing word should be **Lean**, with parenthetical provenance.

Additionally, **rejected theorems** (status=Rejected, including ancestor-cascaded) currently surface in public lists. They should be hidden by default with an opt-in toggle, since most casual viewers do not want to wade through failed candidates.

## Goals

- Filter `chain_replay` rows out of public-facing list endpoints and the public theorem detail endpoint by default.
- Filter `Rejected` rows out of public-facing list endpoints by default; expose them via opt-in query param.
- Replace badge labels with `Lean-verified (server)` / `Lean-verified (worker only) — pending server verification`.
- Treat trusted-worker `worker_claim` rows as "Lean-verified (server)" without altering the underlying `tactic_used` value in the DB.
- Defense-in-depth: if a `chain_replay` row ever leaks past the filter (bug, direct ID lookup, etc.), the badge falls back to a non-confident label rather than rendering as verified.

## Non-Goals

- No change to the verification pipeline. `chain_replay`, `worker_claim`, and `lake_build` remain as today.
- No change to the cascade-reject graph. A trusted-worker row participates in cascading identically to a server-lake-confirmed row, keyed on theorem IDs in the proof DAG.
- No change to the trust model (`trust::resolve_trust`), spot-check sampling, reputation EMA, auto-revoke, or worker submission contract.
- No change to the worker submission API. Soft-accept stays. The current default in `worker.rs:107-122` already requires local lake-build; `--no-local-lake` remains a clearly-labeled DEV-ONLY flag.
- No DB migration. The `theorems.worker_trusted` column already exists (`pg/src/entity/theorems.rs:71`, populated at ingest in `handlers/ingest.rs:389`).
- No change to admin-facing views or metrics. Admins continue to see the full picture, including `chain_replay` and `Rejected` rows.

---

## Design

### Part 1 — Backend visibility filter

A single helper on the theorems query layer applies the public-default filter. The helper is opt-out (callers must explicitly request inclusion), so any new endpoint inherits the safe default.

**New query layer parameters.** Update `pg/src/query/theorems.rs::list_verified` (signature today: `list_verified(pg, cursor, limit, domain)`) and any sibling lister used by public endpoints. Two approaches; pick at implementation time:

- *(A)* Add two trailing bool params `include_internal, include_rejected`. Minimal diff; ugly call sites.
- *(B)* Group all listing options into a `ListOptions { cursor, limit, domain, include_internal, include_rejected }` struct with a `Default`. Cleaner; touches every call site once.

Recommend (B) — the struct will absorb future filter additions without further signature churn.

Filter semantics:

- `include_internal: bool` — when `false` (default), excludes rows where `verification_tactic = 'chain_replay'`.
- `include_rejected: bool` — when `false` (default), excludes rows where `status = 'Rejected'`.

**Endpoints affected** (handler layer reads query params, passes to query layer):

| Endpoint | Default behavior | Opt-in query params |
|---|---|---|
| `GET /api/theorems` (browse list) | Hide chain_replay + Rejected | `?include_rejected=true`, `?include_internal=true` (admin only) |
| `GET /api/discoveries` | Hide chain_replay + Rejected | same |
| `GET /api/search` | Hide chain_replay + Rejected | same |
| `GET /api/theorem/:id` | If `chain_replay`: 404 to anonymous; admin sees normally. Rejected rows return as-is (direct deep links work). | n/a |
| Admin endpoints (`/admin/...`) | Unfiltered | n/a |
| Internal seed export | Already excludes chain_replay; unchanged | n/a |
| Lake-promotion queue, audit log, metrics | Unchanged | n/a |

**Authorization for `?include_internal=true`**: only honored when the request authenticates as admin via the existing `RequireAdmin` extractor (`engine/crates/api/src/admin/require_admin.rs:35` — accepts a session bearing the admin flag OR an `ADMIN_TOKEN` bearer). The handler uses an `Option<RequireAdmin>` extractor: present → param honored; absent → param silently ignored, public default applied. This avoids leaking internal staging rows via crafted query strings.

**Defense-in-depth for direct ID lookup**: `GET /api/theorem/:id` returning 404 for non-admin chain_replay reads mirrors the list-filter posture. If a theorem flips from chain_replay → lake_build (queue drain), the ID becomes resolvable. If it flips chain_replay → Rejected (lake fail), the ID continues to be retrievable as a Rejected row (so deep links from audit logs remain functional).

**Pending rows**: stay visible in public lists. They are short-lived ("submitted, replay queue hasn't run yet") and seeing them gives users useful liveness signal.

### Part 2 — Frontend badge + filter UI

**Badge component** (`nasrudin-frontend/src/components/theorem/VerificationBadge.tsx`).

The component's input grows by one prop:

```ts
interface Props {
  status: string;
  tactic: string | null;
  submitterTrusted: boolean;          // NEW — read from theorems.worker_trusted snapshot
  rejectedReason?: string | null;
  compact?: boolean;
}
```

Rendering rules. The component keeps its existing single-pill structure (`label` + `hint` tooltip). "Pending server verification" appears in the tooltip, not as a second pill — keeps card layouts compact.

| `status` | `tactic` | `submitterTrusted` | Label (visible) | Color | Tooltip (`hint`) |
|---|---|---|---|---|---|
| Verified | `lake_build` | * | **Lean-verified (server)** | gold | "Server ran lake build; Lean kernel confirmed." |
| Verified | `worker_claim` | true | **Lean-verified (server)** | gold | "Trusted worker lake-built locally; server accepts without re-running." |
| Verified | `worker_claim` | false | **Lean-verified (worker)** | blue | "Worker lake-built locally; server lake confirmation pending." |
| Verified | `chain_replay` | * | **Pending** (defense-in-depth fallback) | grey | "Verification still in progress." |
| Pending | * | * | **Pending** | grey | "Submitted; reverify drain has not run yet." |
| Rejected | * (rejected_reason starts with `ancestor_rejected:`) | * | **Cascaded** | red | "An ancestor was rejected; this theorem is invalid by transitivity." |
| Rejected | * (otherwise) | * | **Rejected** | red | "Lake build rejected this theorem." |

The cascade detection logic mirrors the existing component (`VerificationBadge.tsx:36` — `s.rejectedReason?.startsWith('ancestor_rejected:')`). Color palette stays as today: gold for "(server)", blue for "(worker)", red for Rejected/Cascaded, grey for Pending. The third blue "Chain-verified" state is removed from the user-facing palette entirely.

**List filter UI**:

- `/discoveries` and `/browse` get a **"Show rejected"** toggle (off by default). Toggling sets `?include_rejected=true` on the underlying API call. URL-synced so the toggle state survives reload.
- No public-facing toggle for `?include_internal`. Admin views may surface it later (out of scope here).

**Direct theorem-page deep links** (`/theorem/:id`):

- For non-admin viewers hitting a chain_replay ID, the page renders a 404 / "not yet published" state.
- For Rejected IDs, the page renders normally with the Rejected badge — direct links from audit logs / cascade ancestor traces work.

### Part 3 — Surface `worker_trusted` to the frontend

`theorems.worker_trusted` already exists in PG (`engine/crates/pg/src/entity/theorems.rs:67-71`, set at ingest in `engine/crates/api/src/handlers/ingest.rs:389`). The SeaORM `Model` derives `Serialize` and is serialized whole into the `/api/theorems` response (`engine/crates/api/src/handlers/theorems.rs:108-113` — `"theorems": page.items`). So **the field is already on the wire**; the only gap is the frontend TypeScript type.

**Frontend types** (`nasrudin-frontend/src/lib/types.ts`):

Add to the `Theorem` interface:

```ts
/** Trust decision snapshotted at ingest. Drives the badge's "(server)" vs "(worker)"
 * flip for `worker_claim` rows: trusted submitter ⇒ same badge as `lake_build`. */
worker_trusted: boolean;
```

The badge component (`nasrudin-frontend/src/components/theorem/VerificationBadge.tsx`) reads it via the new `submitterTrusted` prop, sourced by the badge's caller as `theorem.worker_trusted`. (Snake_case on the wire matches the existing `Theorem` field convention; camelCase on the prop matches React conventions.)

No DB migration, no new column, no backfill, no API handler changes. Rows older than the `worker_trusted` migration default to `false`, which renders as "Lean-verified (worker) — pending server verification" — the conservative state, correct for legacy rows where we don't have a recorded trust decision.

---

## Cascade Semantics — Confirmation

Cascade-reject keys on theorem IDs in the proof DAG (`parents: Option<Vec<Vec<u8>>>` on `theorems` rows), not on `verification_tactic`. So:

- A trusted-worker auto-promoted row (DB: `tactic=worker_claim, worker_trusted=true`, badge: "Lean-verified (server)") **participates in cascade identically** to a server-lake-confirmed row.
- If a spot check later catches a trusted-worker disagreement and the row gets revoked, descendants cascade the same way they would for any other rejection. The existing logic in `lake_promotion.rs:194-232` (the `was_worker_claim` disagreement path) is untouched.
- Reputation EMA, auto-revoke at reputation < 0.2, the worker_claim disagreement detection — all keep running.

---

## Sources of `chain_replay` Rows (For Reference)

These continue to write chain_replay rows under the new design; only their public visibility changes:

1. **PhysLean catalog importer** — pre-lake staging until the lake worker drains them.
2. **Reverify drain on theorems without a worker claim** (`reverify.rs:206`).
3. **Server-internal GA** evolution (any tree the Rust replay accepts but server hasn't lake-built yet).
4. **Dev workers running `--no-local-lake`** (warned, intended for dev only).

All four are legitimate "lake build pending" states.

---

## Verification

### Backend

- Unit tests on the new query helpers (`list_verified` etc.) covering the three filter combinations: default (hide both), `include_rejected=true`, `include_internal=true` with admin context, `include_internal=true` without admin context (silently ignored).
- Integration test: insert one row of each `(status, tactic)` combination, hit `/api/theorems`, assert only `Verified` non-`chain_replay` rows come back.
- Integration test: `GET /api/theorem/:id` for a chain_replay row returns 404 to anonymous, 200 to admin.

### Frontend

- Component tests on `VerificationBadge`: each of the 7 rendering rules in the table above renders the expected label, tooltip, and color.
- Component test: chain_replay leak — pass `tactic="chain_replay"` and assert the component does NOT render any "Lean-verified" label.
- Smoke test: `/discoveries` page with the "Show rejected" toggle off shows no Rejected rows; toggled on, they appear with the Rejected/Cascaded badge.

### Manual

- Spin up the dev stack, browse `/discoveries` — confirm no chain_replay rows visible, no Rejected rows visible.
- Toggle "Show rejected" — confirm Rejected/Cascaded rows appear with red badges.
- As an admin, hit `/api/theorems?include_internal=true` — confirm chain_replay rows surface.
- Deep-link to a known Rejected theorem ID directly via `/theorem/:id` — page renders with Rejected badge.
- Deep-link to a known chain_replay theorem ID as a non-admin — page returns 404.

---

## Out of Scope (Explicitly Deferred)

- Any tightening of the worker submission contract (e.g., reject `worker_verified=false` submissions). The current soft-accept behavior is correct: server-internal paths legitimately produce chain_replay rows.
- New "trusted worker" tactic enum value. Option 2 from brainstorming was chosen — keep `tactic_used="worker_claim"` in DB, derive badge from `(tactic, worker_trusted)`.
- Admin UI for browsing chain_replay rows. May be added later; not required to ship the public-facing change.
- Migration / re-tagging of historic chain_replay rows. They will stay chain_replay in DB until the lake-promotion queue drains them.
- Changes to seed export, metrics, audit log. All already correctly distinguish the three tactic values.
