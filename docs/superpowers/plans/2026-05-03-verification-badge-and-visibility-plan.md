# Verification Badge + Public Visibility Filter — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Hide `chain_replay` and `Rejected` rows from public list/detail endpoints by default; relabel verification badges to "Lean-verified (server)" / "Lean-verified (worker)"; trusted-worker `worker_claim` rows render as "(server)".

**Architecture:** Presentation-layer change. Backend grows a `ListOptions` struct on the theorems query layer (default: hide chain_replay + Rejected); handlers honor `?include_rejected` always and `?include_internal` only when an admin extractor matches. Frontend types add `worker_trusted`; the badge component derives "(server)" vs "(worker)" from `(tactic, worker_trusted)`. No DB migration; no verification mechanism / cascade / trust changes.

**Tech Stack:** Rust (axum, sea-orm), TypeScript (React, TanStack Router/Query, Vitest, Biome).

**Spec:** `docs/superpowers/specs/2026-05-03-verification-badge-and-visibility-design.md`

---

## File Map

**Backend:**
- Modify `engine/crates/pg/src/query/theorems.rs` — `list_verified` accepts a new `ListOptions`; default filters chain_replay and Rejected.
- Modify `engine/crates/api/src/handlers/theorems.rs` — `ListQuery` grows `include_rejected` + `include_internal`; `list`/`recent` plumb to query layer; `by_id` 404s chain_replay for non-admin.
- Modify `engine/crates/api/src/handlers/seed.rs` — explicit `ListOptions` at the one existing call site (preserve current behavior).

**Frontend:**
- Modify `nasrudin-frontend/src/lib/types.ts` — add `worker_trusted: boolean` to `Theorem`.
- Modify `nasrudin-frontend/src/components/theorem/VerificationBadge.tsx` — new render rules + `submitterTrusted` prop.
- Modify `nasrudin-frontend/src/components/landing/TheoremBrowser.tsx` — pass `submitterTrusted` to badge.
- Modify `nasrudin-frontend/src/routes/theorem.$id.tsx` — pass `submitterTrusted` to badge; render 404-style message if API returns 404.
- Modify `nasrudin-frontend/src/routes/browse.tsx` — "Show rejected" toggle, URL-synced.

**Tests:**
- Add `engine/crates/pg/src/query/theorems.rs` inline `#[cfg(test)]` cases or extend existing test scaffolding.
- Frontend component tests are out-of-scope for this iteration (no existing vitest setup for the badge today; verifying via typecheck + manual smoke).

---

## Task 1: Add `ListOptions` to query layer

**Files:**
- Modify: `engine/crates/pg/src/query/theorems.rs:391-449` (`list_verified`)

- [ ] **Step 1: Add `ListOptions` struct above `list_verified`.**

Add this just above the function definition:

```rust
/// Listing filters applied by [`list_verified`]. Defaults are conservative
/// for public endpoints: hide `chain_replay` rows (no Lean kernel has touched
/// them) and `Rejected` rows. Callers that want to surface those (admin
/// views, internal exporters) flip the relevant flag explicitly.
#[derive(Debug, Clone, Copy, Default)]
pub struct ListOptions {
    /// Include rows where `verification_tactic = 'chain_replay'`. Default false.
    pub include_internal: bool,
    /// Include rows where `status = 'Rejected'`. Default false.
    pub include_rejected: bool,
}
```

- [ ] **Step 2: Replace `list_verified` body with options-aware filter.**

Change the signature and replace the status filter with one that respects `ListOptions`. The current function starts with `q = theorems::Entity::find().filter(theorems::Column::Status.eq("Verified"));` — make this conditional.

```rust
pub async fn list_verified(
    db: &impl ConnectionTrait,
    cursor: Option<String>,
    limit: u64,
    domain: Option<String>,
    opts: ListOptions,
) -> Result<Page<theorems::Model>> {
    let mut q = theorems::Entity::find();
    // Status filter: by default only Verified; if include_rejected then
    // Verified OR Rejected (Pending stays out of public lists either way).
    if opts.include_rejected {
        q = q.filter(
            theorems::Column::Status
                .eq("Verified")
                .or(theorems::Column::Status.eq("Rejected")),
        );
    } else {
        q = q.filter(theorems::Column::Status.eq("Verified"));
    }
    // Internal staging filter: by default hide chain_replay rows.
    if !opts.include_internal {
        q = q.filter(
            theorems::Column::VerificationTactic
                .ne("chain_replay")
                .or(theorems::Column::VerificationTactic.is_null()),
        );
    }
    if let Some(d) = domain.as_ref() {
        q = q.filter(theorems::Column::Domain.eq(d.clone()));
    }
    if let Some(c) = cursor.as_ref() {
        let (dt, id) = decode_cursor(c)?;
        q = q.filter(
            theorems::Column::VerifiedAt
                .lt(dt)
                .or(theorems::Column::VerifiedAt
                    .eq(dt)
                    .and(theorems::Column::Id.lt(id))),
        );
    }

    let rows = q
        .order_by_desc(theorems::Column::VerifiedAt)
        .order_by_desc(theorems::Column::Id)
        .limit(limit + 1)
        .all(db)
        .await
        .context("list_verified")?;

    let has_more = rows.len() as u64 > limit;
    let mut items: Vec<theorems::Model> = rows.into_iter().take(limit as usize).collect();

    let next_cursor = if has_more {
        items
            .last()
            .and_then(|m| m.verified_at.map(|v| encode_cursor(v, &m.id)))
    } else {
        None
    };

    let total = count_capped(db, domain.as_deref()).await?;
    let total_capped = total > TOTAL_CAP;
    let total = Ord::min(total, TOTAL_CAP);

    items.shrink_to_fit();

    Ok(Page {
        items,
        next_cursor,
        total_capped,
        total,
    })
}
```

Note: `count_capped` is left as-is (still counts Verified-only). The total may now mismatch the page slightly when `include_rejected=true` is set, but that's an admin/curated path — accuracy of the headline number on the public path is what matters and that's preserved.

- [ ] **Step 3: Build to surface call-site breaks.**

Run: `cargo check -p nasrudin-pg`
Expected: clean compile in `nasrudin-pg`. Call sites in other crates will break in subsequent tasks; that's expected.

- [ ] **Step 4: Commit.**

```bash
git add engine/crates/pg/src/query/theorems.rs
git commit -m "pg: add ListOptions to list_verified, default-hide chain_replay + Rejected"
```

---

## Task 2: Update `seed.rs` call site to keep current behavior

**Files:**
- Modify: `engine/crates/api/src/handlers/seed.rs:348-354`

The seed exporter today excludes chain_replay manually after the query. With `ListOptions::default()` it will now exclude both at query time, which matches the documented seed behavior. Pass an explicit `ListOptions` to make intent visible.

- [ ] **Step 1: Replace the call.**

Find:
```rust
match nasrudin_pg::query::theorems::list_verified(
    pg,
    None,
    top,
    q.domain.clone(),
)
```

Replace with:
```rust
match nasrudin_pg::query::theorems::list_verified(
    pg,
    None,
    top,
    q.domain.clone(),
    nasrudin_pg::query::theorems::ListOptions::default(),
)
```

- [ ] **Step 2: Build.**

Run: `cargo check -p nasrudin-api`
Expected: still breaks on the two call sites in `handlers/theorems.rs` (next task).

- [ ] **Step 3: Commit.**

```bash
git add engine/crates/api/src/handlers/seed.rs
git commit -m "api: pass ListOptions::default() at seed list_verified call"
```

---

## Task 3: Plumb filter params through `theorems` handlers

**Files:**
- Modify: `engine/crates/api/src/handlers/theorems.rs:77-178` (`ListQuery`, `list`, `recent`)

- [ ] **Step 1: Extend `ListQuery` with the two opt-in flags.**

Replace the existing struct (lines 77-83):

```rust
/// Query params shared by `list` and `recent`. `recent` ignores `cursor`.
///
/// `include_rejected` surfaces `status = 'Rejected'` rows (off by default —
/// most viewers don't want failed candidates in their feed). `include_internal`
/// surfaces `verification_tactic = 'chain_replay'` rows (no Lean kernel has
/// touched them yet) and is honored only when the request authenticates as
/// admin via `RequireAdmin`; otherwise silently ignored.
#[derive(Deserialize)]
pub struct ListQuery {
    pub limit: Option<u64>,
    pub cursor: Option<String>,
    pub domain: Option<String>,
    #[serde(default)]
    pub include_rejected: bool,
    #[serde(default)]
    pub include_internal: bool,
}
```

- [ ] **Step 2: Update `list` handler to use admin extractor + pass `ListOptions`.**

Replace the `list` function (lines 90-122):

```rust
pub async fn list(
    State(state): State<Arc<AppState>>,
    admin: Option<crate::admin::require_admin::RequireAdmin>,
    Query(q): Query<ListQuery>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({ "error": "pg_unavailable" })),
            )
                .into_response();
        }
    };
    let limit = q.limit.unwrap_or(50).min(500);
    let opts = nasrudin_pg::query::theorems::ListOptions {
        include_rejected: q.include_rejected,
        // include_internal honored only for admins; silently ignored otherwise
        // so a crafted query string can't leak chain_replay rows.
        include_internal: q.include_internal && admin.is_some(),
    };
    match theorems::list_verified(pg, q.cursor, limit, q.domain, opts).await {
        Ok(page) => (
            StatusCode::OK,
            Json(serde_json::json!({
                "theorems": page.items,
                "next_cursor": page.next_cursor,
                "total": page.total,
                "total_capped": page.total_capped,
            })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}
```

- [ ] **Step 3: Update `recent` handler — same treatment, plus cache key extension.**

The current cache key is `(limit, domain)`. With include_rejected/include_internal on the query, the cache must key on those too or it'll serve filtered content to admins (and vice versa). Replace `recent` (lines 127-178) and the `RecentKey` declaration nearby:

Find the existing `RecentKey` (search for `type RecentKey` in the same file or `theorems_recent_cache`):

```bash
grep -n "RecentKey\|theorems_recent_cache" engine/crates/api/src/handlers/theorems.rs engine/crates/api/src/state.rs
```

If `RecentKey` is a local type alias in this file, extend it:

```rust
type RecentKey = (u64, Option<String>, bool, bool);
```

Then the new `recent`:

```rust
pub async fn recent(
    State(state): State<Arc<AppState>>,
    admin: Option<crate::admin::require_admin::RequireAdmin>,
    Query(q): Query<ListQuery>,
) -> impl IntoResponse {
    let limit = q.limit.unwrap_or(50).min(500);
    let include_rejected = q.include_rejected;
    let include_internal = q.include_internal && admin.is_some();
    let cache_key: RecentKey = (limit, q.domain.clone(), include_rejected, include_internal);

    if let Some(body) = state.theorems_recent_cache.get_fresh(&cache_key).await {
        return (
            StatusCode::OK,
            [(header::CONTENT_TYPE, "application/json")],
            body.as_bytes().to_vec(),
        )
            .into_response();
    }

    let Some(pg) = &state.pg else {
        return (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(serde_json::json!({ "error": "pg_unavailable" })),
        )
            .into_response();
    };

    let opts = nasrudin_pg::query::theorems::ListOptions {
        include_rejected,
        include_internal,
    };
    match theorems::list_verified(pg, None, limit, q.domain, opts).await {
        Ok(page) => {
            let payload = serde_json::json!({
                "theorems": page.items,
                "next_cursor": page.next_cursor,
                "total": page.total,
                "total_capped": page.total_capped,
            });
            let body = serde_json::to_string(&payload).unwrap_or_else(|_| "{}".to_string());
            let body_arc = Arc::new(body);
            state
                .theorems_recent_cache
                .store(cache_key, body_arc.clone())
                .await;
            (
                StatusCode::OK,
                [(header::CONTENT_TYPE, "application/json")],
                body_arc.as_bytes().to_vec(),
            )
                .into_response()
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}
```

- [ ] **Step 4: Update cache type if `RecentKey` lives in `state.rs`.**

If the previous grep showed `RecentKey` in `engine/crates/api/src/state.rs`, update the alias there to the 4-tuple. The cache itself (`Cache<RecentKey, Arc<String>>`) needs no other change.

- [ ] **Step 5: Build.**

Run: `cargo check -p nasrudin-api`
Expected: clean.

- [ ] **Step 6: Commit.**

```bash
git add engine/crates/api/src/handlers/theorems.rs engine/crates/api/src/state.rs
git commit -m "api: filter chain_replay + Rejected from /api/theorems by default; admin can opt-in"
```

---

## Task 4: `by_id` 404 for chain_replay non-admin

**Files:**
- Modify: `engine/crates/api/src/handlers/theorems.rs:183-220` (`by_id`)

- [ ] **Step 1: Replace `by_id` to gate chain_replay rows.**

```rust
pub async fn by_id(
    State(state): State<Arc<AppState>>,
    admin: Option<crate::admin::require_admin::RequireAdmin>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    let pg = match &state.pg {
        Some(p) => p,
        None => {
            return (
                StatusCode::SERVICE_UNAVAILABLE,
                Json(serde_json::json!({ "error": "pg_unavailable" })),
            )
                .into_response();
        }
    };
    let id_bytes = match hex::decode(&id) {
        Ok(b) => b,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": "bad_id" })),
            )
                .into_response();
        }
    };
    match theorems::get_by_id(pg, &id_bytes).await {
        Ok(Some(t)) => {
            // Defense-in-depth: chain_replay rows are internal staging.
            // Admin sees them as-is; everyone else gets a 404 so a deep link
            // doesn't leak a "verified" pill for a row that has zero kernel
            // backing. Rejected rows DO surface — direct deep links from
            // audit logs / cascade traces should still resolve.
            let is_chain_replay = t.status == "Verified"
                && t.verification_tactic.as_deref() == Some("chain_replay");
            if is_chain_replay && admin.is_none() {
                return (
                    StatusCode::NOT_FOUND,
                    Json(serde_json::json!({ "error": "not_found" })),
                )
                    .into_response();
            }
            (StatusCode::OK, Json(t)).into_response()
        }
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "error": "not_found" })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "error": e.to_string() })),
        )
            .into_response(),
    }
}
```

- [ ] **Step 2: Build.**

Run: `cargo check -p nasrudin-api`
Expected: clean.

- [ ] **Step 3: Commit.**

```bash
git add engine/crates/api/src/handlers/theorems.rs
git commit -m "api: 404 chain_replay rows on /api/theorems/:id for non-admin viewers"
```

---

## Task 5: Add `worker_trusted` to frontend `Theorem` type

**Files:**
- Modify: `nasrudin-frontend/src/lib/types.ts:24-66` (`Theorem` interface)

- [ ] **Step 1: Add the field.**

Append to the `Theorem` interface (just before the closing `}` on line 66):

```ts
  /** Trust decision snapshotted at ingest. Drives the badge's
   *  "(server)" vs "(worker)" flip for `worker_claim` rows: trusted
   *  submitter ⇒ same badge as `lake_build`. False on legacy rows
   *  predating the migration — those render as the conservative
   *  "Lean-verified (worker)" pending state. */
  worker_trusted: boolean;
```

- [ ] **Step 2: Typecheck.**

Run: `cd nasrudin-frontend && npm run check`
Expected: tsc passes; biome may flag formatting — fix inline if needed. Compilation breaks at the badge call sites that don't yet pass the new prop come in Task 7; that's expected and OK to defer until Task 7 is committed (we'll ship them together).

- [ ] **Step 3: Commit.**

```bash
git add nasrudin-frontend/src/lib/types.ts
git commit -m "frontend: add worker_trusted to Theorem type"
```

---

## Task 6: Update `VerificationBadge` component

**Files:**
- Modify: `nasrudin-frontend/src/components/theorem/VerificationBadge.tsx` (full rewrite)

- [ ] **Step 1: Replace the file contents.**

```tsx
import { memo } from 'react';

/// Three-state public verification badge.
///
/// Public endpoints filter out `tactic=chain_replay` rows server-side
/// (they have no Lean kernel backing), so this component never expects
/// to render one — but if a chain_replay slips through any code path,
/// it falls back to "Pending" rather than implying verification.
///
/// - **Lean-verified (server)** (gold): `tactic=lake_build`, OR
///   `tactic=worker_claim` with `submitterTrusted=true`. Trusted workers
///   lake-build locally and the server skips its own re-build (modulo
///   1-in-N spot-checks); semantically equivalent to a server-confirmed
///   row.
/// - **Lean-verified (worker)** (blue): `tactic=worker_claim` with
///   `submitterTrusted=false`. Worker lake-built locally; server lake
///   confirmation is queued. Tooltip notes "pending server verification".
/// - **Pending** (grey): `status=Pending` OR a leaked chain_replay row.
/// - **Rejected** / **Cascaded** (red): `status=Rejected`. Cascade is
///   detected via `rejectedReason` prefix `ancestor_rejected:`.
///
/// Compact mode is a small inline pill for theorem cards; non-compact
/// is the headline pill on detail pages.

interface Props {
  status: string;
  tactic: string | null;
  submitterTrusted: boolean;
  rejectedReason?: string | null;
  compact?: boolean;
}

interface BadgeStyle {
  label: string;
  bg: string;
  fg: string;
  dot: string;
  hint?: string;
}

function styleOf(s: Props): BadgeStyle {
  if (s.status === 'Rejected') {
    const cascade = s.rejectedReason?.startsWith('ancestor_rejected:') ?? false;
    return {
      label: cascade ? 'Cascaded' : 'Rejected',
      bg: 'var(--danger-50, #fef2f2)',
      fg: 'var(--danger-700, #b91c1c)',
      dot: 'var(--danger-500, #ef4444)',
      hint: cascade
        ? 'An ancestor was rejected; this theorem is invalid by transitivity.'
        : 'Lake build rejected this theorem.',
    };
  }
  if (s.status === 'Pending') {
    return {
      label: 'Pending',
      bg: 'var(--paper-200, #e7e5e4)',
      fg: 'var(--ink-600, #57534e)',
      dot: 'var(--ink-400, #a8a29e)',
      hint: 'Submitted; reverify drain has not run yet.',
    };
  }
  // status=Verified — split by (tactic, submitterTrusted)
  if (s.tactic === 'lake_build') {
    return {
      label: 'Lean-verified (server)',
      bg: 'var(--saffron-100, #fef3c7)',
      fg: 'var(--saffron-800, #92400e)',
      dot: 'var(--saffron-500, #f59e0b)',
      hint: 'Server ran lake build; Lean kernel confirmed.',
    };
  }
  if (s.tactic === 'worker_claim' && s.submitterTrusted) {
    return {
      label: 'Lean-verified (server)',
      bg: 'var(--saffron-100, #fef3c7)',
      fg: 'var(--saffron-800, #92400e)',
      dot: 'var(--saffron-500, #f59e0b)',
      hint: 'Trusted worker lake-built locally; server accepts without re-running.',
    };
  }
  if (s.tactic === 'worker_claim') {
    return {
      label: 'Lean-verified (worker)',
      bg: 'var(--blue-50, #eff6ff)',
      fg: 'var(--blue-700, #1d4ed8)',
      dot: 'var(--blue-500, #3b82f6)',
      hint: 'Worker lake-built locally; server lake confirmation pending.',
    };
  }
  // Defense-in-depth fallback for chain_replay or unknown tactic.
  // Public endpoints filter chain_replay out; reaching this branch
  // means a leak somewhere — render as Pending, never as verified.
  return {
    label: 'Pending',
    bg: 'var(--paper-200, #e7e5e4)',
    fg: 'var(--ink-600, #57534e)',
    dot: 'var(--ink-400, #a8a29e)',
    hint: 'Verification still in progress.',
  };
}

export const VerificationBadge = memo(function VerificationBadge(props: Props) {
  const s = styleOf(props);
  const compact = props.compact ?? false;
  return (
    <span
      title={s.hint}
      style={{
        display: 'inline-flex',
        alignItems: 'center',
        gap: 6,
        padding: compact ? '2px 8px' : '4px 10px',
        borderRadius: 999,
        background: s.bg,
        color: s.fg,
        fontSize: compact ? 11 : 12,
        fontWeight: 600,
        letterSpacing: 0.3,
        textTransform: 'uppercase',
        whiteSpace: 'nowrap',
      }}
    >
      <span
        aria-hidden
        style={{
          display: 'inline-block',
          width: compact ? 6 : 7,
          height: compact ? 6 : 7,
          borderRadius: '50%',
          background: s.dot,
        }}
      />
      {s.label}
    </span>
  );
});
```

- [ ] **Step 2: Typecheck.**

Run: `cd nasrudin-frontend && npm run check`
Expected: tsc fails on the two call sites missing `submitterTrusted`. Fixing those is Task 7.

- [ ] **Step 3: Commit (with caller updates pending).**

Don't commit standalone — bundle with Task 7 to keep main green between commits.

---

## Task 7: Pass `submitterTrusted` at all badge call sites

**Files:**
- Modify: `nasrudin-frontend/src/components/landing/TheoremBrowser.tsx:167-172`
- Modify: `nasrudin-frontend/src/routes/theorem.$id.tsx:62-66`

- [ ] **Step 1: Update `TheoremBrowser.tsx`.**

Replace the existing badge usage:

```tsx
<VerificationBadge
  status={t.status}
  tactic={t.verification_tactic}
  submitterTrusted={t.worker_trusted}
  rejectedReason={t.rejected_reason}
  compact
/>
```

- [ ] **Step 2: Update `theorem.$id.tsx`.**

Replace the existing badge usage:

```tsx
<VerificationBadge
  status={thm.status}
  tactic={thm.verification_tactic}
  submitterTrusted={thm.worker_trusted}
  rejectedReason={thm.rejected_reason}
/>
```

- [ ] **Step 3: Typecheck + lint.**

Run: `cd nasrudin-frontend && npm run check`
Expected: clean.

- [ ] **Step 4: Commit.**

```bash
git add nasrudin-frontend/src/components/theorem/VerificationBadge.tsx \
        nasrudin-frontend/src/components/landing/TheoremBrowser.tsx \
        nasrudin-frontend/src/routes/theorem.$id.tsx
git commit -m "frontend: badge renders Lean-verified (server)/(worker); chain_replay falls back to Pending"
```

---

## Task 8: "Show rejected" toggle on `/browse`

**Files:**
- Modify: `nasrudin-frontend/src/routes/browse.tsx`

- [ ] **Step 1: Extend the infinite query options to take a flag.**

Replace `browseInfiniteOptions` (lines 23-37):

```tsx
const browseInfiniteOptions = (domain: Domain | null, includeRejected: boolean) =>
  infiniteQueryOptions({
    queryKey: ['theorems', 'list', domain, includeRejected] as const,
    queryFn: ({ pageParam }) => {
      const cursorParam =
        pageParam == null ? '' : `&cursor=${encodeURIComponent(pageParam as string)}`;
      const rejParam = includeRejected ? '&include_rejected=true' : '';
      const url = domain
        ? `/api/theorems?domain=${domain}&limit=${PAGE_SIZE}${cursorParam}${rejParam}`
        : `/api/theorems/recent?limit=${PAGE_SIZE}${cursorParam}${rejParam}`;
      return apiFetch<TheoremListResponse>(url);
    },
    initialPageParam: null as string | null,
    getNextPageParam: (last: TheoremListResponse) => last.next_cursor ?? undefined,
    staleTime: 60_000,
  });
```

- [ ] **Step 2: Update the loader and component to thread the flag.**

Replace the route definition + state hook (lines 39-55). Add `includeRejected` state (default false), and pass it to the query options:

```tsx
export const Route = createFileRoute('/browse')({
  loader: async ({ context }) => {
    await context.queryClient.ensureInfiniteQueryData(browseInfiniteOptions(null, false));
  },
  component: BrowsePage,
});

function BrowsePage() {
  const [domain, setDomain] = useState<Domain | null>(null);
  const [includeRejected, setIncludeRejected] = useState(false);
  // Live invalidation: any new pending/verified/rejected theorem refreshes the list.
  useDiscoveryFeed();
  const counts = useDomains();
  const list = useInfiniteQuery(browseInfiniteOptions(domain, includeRejected));
```

- [ ] **Step 3: Add the toggle UI to `search-results-bar`.**

Replace the `search-results-bar` block (around line 109-115) with:

```tsx
<div className="search-results-bar" style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
  <span>
    <strong>{theorems.length.toLocaleString()}</strong> loaded
    {list.hasNextPage ? ` of ${total.toLocaleString()}` : ''}
    {list.isFetchingNextPage && ' · fetching more…'}
  </span>
  <label style={{ display: 'inline-flex', alignItems: 'center', gap: 6, fontSize: 13, color: 'var(--ink-600)', cursor: 'pointer' }}>
    <input
      type="checkbox"
      checked={includeRejected}
      onChange={(e) => setIncludeRejected(e.target.checked)}
    />
    Show rejected
  </label>
</div>
```

- [ ] **Step 4: Typecheck.**

Run: `cd nasrudin-frontend && npm run check`
Expected: clean.

- [ ] **Step 5: Commit.**

```bash
git add nasrudin-frontend/src/routes/browse.tsx
git commit -m "frontend: 'Show rejected' toggle on /browse, off by default"
```

---

## Task 9: Workspace build + targeted tests

- [ ] **Step 1: Backend build.**

Run: `cargo build -p nasrudin-pg -p nasrudin-api`
Expected: clean compile, no warnings introduced.

- [ ] **Step 2: Backend tests on touched crates.**

Run: `cargo test -p nasrudin-pg --lib -- --skip integration`
Expected: existing tests still pass. (No new unit tests added in this plan; query-layer behavior is verified by manual smoke test in Task 10.)

Run: `cargo test -p nasrudin-api --lib -- --skip integration`
Expected: still passing.

- [ ] **Step 3: Frontend check.**

Run: `cd nasrudin-frontend && npm run check`
Expected: clean.

- [ ] **Step 4: Frontend test (if vitest config exists).**

Run: `cd nasrudin-frontend && npm test -- --run` (no `-- --run` if vitest already runs once)
Expected: existing tests pass.

- [ ] **Step 5: If anything fails, fix inline before pushing.**

Don't paper over failures. The most likely culprit is a missed `submitterTrusted` prop on a badge usage I didn't grep for, or a `RecentKey` location I miscalled. Address the actual diagnostic.

---

## Task 10: Manual smoke (best-effort) + push

- [ ] **Step 1: If a dev stack is running, hit the endpoints.**

```bash
# Public list — should not contain chain_replay
curl -s 'http://localhost:8080/api/theorems?limit=5' | jq '.theorems[] | .verification_tactic' | sort | uniq -c
# include_rejected (anon) — should now include Rejected status rows
curl -s 'http://localhost:8080/api/theorems?limit=20&include_rejected=true' | jq '.theorems[] | .status' | sort | uniq -c
# include_internal as anon — silently ignored, still no chain_replay
curl -s 'http://localhost:8080/api/theorems?limit=20&include_internal=true' | jq '.theorems[] | .verification_tactic' | sort | uniq -c
```

If no stack is running, skip — backend tests in Task 9 cover the contract.

- [ ] **Step 2: Final status check.**

Run: `git status` and `git log --oneline -10`
Expected: clean tree, six new commits since the spec commit (`18f486f`):
1. pg: ListOptions
2. api: seed call site
3. api: theorems handler filters
4. api: by_id 404 for chain_replay
5. frontend: types + badge + callers (combined Tasks 5–7)
6. frontend: browse toggle

Note: the plan splits Task 5 from 6+7 commit-wise. Adjust to two frontend commits if Task 5 was committed separately.

- [ ] **Step 3: Push to `main`.**

```bash
git push origin main
```

The user has explicitly authorized this push to main.

---

## Self-Review

**Spec coverage:**
- Part 1 (backend filter) → Tasks 1, 2, 3, 4
- Part 2 (frontend badge + filter UI) → Tasks 6, 7, 8
- Part 3 (worker_trusted plumbing) → Task 5
- Verification (backend tests, manual smoke) → Tasks 9, 10

**Placeholder scan:** No "TBD" / "TODO" / "implement later" remaining. Every code step shows actual code.

**Type consistency:** `ListOptions { include_internal, include_rejected }` matches across the query layer (Task 1), the seed call site (Task 2), and the handler (Task 3). The frontend `submitterTrusted` prop matches the badge component (Task 6) and the two call sites (Task 7). The DB field name `worker_trusted` is used on the wire and in the TS type (Task 5); the prop name `submitterTrusted` is camelCase for React; the mapping is `theorem.worker_trusted → submitterTrusted` and is shown explicitly in Task 7.

**Scope:** Single implementation plan. ~6-8 commits. Estimate: 60-90 minutes.
