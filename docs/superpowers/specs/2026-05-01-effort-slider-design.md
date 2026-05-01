# Effort slider — researcher-controlled lake-slot-hour budget per conjecture

**Status:** spec
**Date:** 2026-05-01
**Owner:** nasrudin

## Problem

Today every paid Researcher conjecture is hardcoded to `lake_slot_hours_quota = 96` (4 lake slots × 24 h) and `slice_priority = 5`. There is no way for a researcher to spend more compute on a conjecture they care about, even if their plan tier grants them more credits than they have queued conjectures. A user with 10 credits/period and one ambitious hunch is forced to either let it die at 96 slot-h or cancel-and-resubmit-and-cancel-and-resubmit.

The quota and priority are already per-row on `conjecture_jobs` — what's missing is a way for the researcher to set them at submit time and a credit-cost model that scales accordingly.

## Decisions

These were settled during brainstorming on 2026-05-01:

| Q | Decision |
|---|---|
| How is extra effort paid for? | **Multi-credit jobs.** Each credit = 96 slot-h. Total cost is debited at submit. |
| Does spending more raise priority? | **Two independent knobs.** Budget slider plus a separate rush toggle. |
| Range of the budget slider? | **1 to user's remaining credits** (dynamic max). |
| Shape of rush? | **Single toggle.** Off = priority 5, On = priority 6, costs +1 credit. |
| Mid-flight top-up? | **No.** Quota is locked at submit. |
| Refund rule? | **Proportional, gated on zero verified.** `floor(credits_spent × (1 - consumed/quota))` if `verified == 0`, else 0. |
| Existing `attempted < 1000` gate? | **Drop it.** `consumed/quota` is the direct measurement; `attempted` was a stale proxy. |

## Architecture

A paid conjecture is now sized at submit by two knobs:

- **Budget** — slider in 1-credit increments, 1 ≤ budget ≤ `me.research_credits_remaining`. Each credit buys 96 lake-slot-hours of cluster time. The chosen value is multiplied by 96 and persisted as `conjecture_jobs.lake_slot_hours_quota`.
- **Rush** — boolean. When set, the row's `slice_priority` is `6` instead of the default `5`, and total cost is incremented by 1.

`total_credits = credits_budget + (rush ? 1 : 0)` is debited atomically at submit. Nothing changes mid-flight.

On cancel, if no theorems were verified, the user receives `floor(credits_spent × (1 - consumed/quota))` credits back, where `credits_spent` is reconstructed from the row (`quota / 96` plus 1 if `slice_priority > 5`). If any theorem was verified, no refund.

## Data model

Zero schema changes. Migration `m20260501_000002_paid_job_quota` already added the four columns we need (`lake_slot_hours_quota`, `lake_slot_hours_consumed`, `slice_priority`, `tier`) and the queue index.

The two helpers in `nasrudin_pg::query::users` gain an `n: u32` parameter:

- `try_decrement_research_credits_n(pg_or_txn, user_id, n) -> Option<u32>` — returns the new remaining count when the predicate `remaining >= n` holds, else `None`. Uses `RETURNING research_credits_remaining` so the caller can echo the fresh value back to clients on 402.
- `refund_research_credits_n(pg_or_txn, user_id, n) -> ()` — increments by `n`. Pure additive update.

The single-credit callers either pass `n=1` directly or get thin wrappers — implementation choice during planning.

## API surface

### `POST /api/research/jobs` — request body grows two optional fields

```json
{
  "hunch": "E = m c^2",
  "domain_hint": "special_relativity",
  "credits_budget": 1,
  "rush": false
}
```

Both new fields are optional with defaults that reproduce today's behavior (`credits_budget = 1`, `rush = false`).

**Validation:**

1. `credits_budget` must be ≥ 1. Reject with `400 invalid_credits_budget` if zero. Negative values are rejected by serde (`u32` deserialise).
2. `n = credits_budget + (rush ? 1 : 0)` is computed.
3. The whole submit is one Postgres transaction:
   ```rust
   let txn = pg.begin().await?;
   let row = try_decrement_research_credits_n(&mut *txn, user_id, n).await?;
   let Some(_) = row else {
       let remaining = read_remaining(&mut *txn, user_id).await?;
       txn.rollback().await?;
       return 402 with body { error: "insufficient_research_credits", required: n, remaining };
   };
   am.lake_slot_hours_quota = Set(96 * credits_budget);
   am.slice_priority = Set(5 + if rush { 1 } else { 0 });
   am.insert(&txn).await?;
   txn.commit().await?;
   ```
4. The decrement and the row insert participate in the same transaction. Rollback unwinds the decrement automatically — no `refund_research_credit` on insert failure is needed.

**Concurrency:** the `UPDATE users ... WHERE remaining >= $n` predicate inside the transaction is a Postgres row-level lock; two parallel requests serialize and only one can satisfy the predicate when there isn't enough headroom. The 402 body returns `{required, remaining}` so the UI can re-sync without a separate `/api/me` round-trip.

**No new endpoints.** Top-up was deferred. Lifecycle stays: create / list / detail / events / cancel.

### `POST /api/research/jobs/{id}/cancel` — single idempotent transaction

Replace the current three-step (read → release_paid_claim → refund) with one transaction whose terminalising UPDATE is the only place the refund decision is made:

```sql
BEGIN;

WITH cancelled AS (
  UPDATE conjecture_jobs
     SET state = 'cancelled',
         completed_at = now()
   WHERE id = $job_id
     AND owner_id = $user_id
     AND state IN ('queued', 'claimed', 'running')
   RETURNING lake_slot_hours_quota,
            lake_slot_hours_consumed,
            candidates_verified,
            allocated_slots,
            slice_priority,
            ((lake_slot_hours_quota / 96)
              + CASE WHEN slice_priority > 5 THEN 1 ELSE 0 END) AS credits_spent
)
UPDATE users
   SET research_credits_remaining = research_credits_remaining + (
     SELECT CASE
       WHEN candidates_verified = 0 THEN
         FLOOR(
           credits_spent::float
           * GREATEST(0.0, 1.0 - (lake_slot_hours_consumed / lake_slot_hours_quota::float))
         )::int
       ELSE 0
     END
     FROM cancelled
   )
 WHERE id = $user_id
   AND EXISTS (SELECT 1 FROM cancelled)
RETURNING research_credits_remaining;

COMMIT;
```

**Properties:**

- **Idempotent against double-clicks.** The conditional `UPDATE conjecture_jobs ... WHERE state IN (...)` ensures only the first racer transitions the row. The second sees zero rows and the second `UPDATE users` `EXISTS` guard prevents a phantom refund. The HTTP handler reads the affected-row count to decide the response: zero rows → `409 terminal_state`; one row → `200 {cancelled: true, refunded_credits: <delta>}`.
- **Heartbeat race closed.** Reading `lake_slot_hours_consumed` inside the same `RETURNING` snapshots it at the exact moment of state transition. Concurrent heartbeats either land before (delta reflected in snapshot) or after (their own `WHERE state IN ('claimed','running')` no-ops because the row is now `cancelled` — verify the heartbeat path's WHERE clause includes the state guard during implementation).
- **Refund formula.** `credits_spent` is reconstructed: budget = `quota / 96` (always exact since quota was set as `96 * budget`), plus 1 if `slice_priority > 5` (rush). No new column.
- **Overshoot clamp.** `GREATEST(0.0, 1.0 - consumed/quota)` clamps to zero if a lying worker pushed `consumed` past `quota`.

**Slot-pool release** (`state.capacity.release_paid_slots`) stays *outside* the transaction — it's in-process state, not DB. The handler reads `allocated_slots` from the `RETURNING` and releases that count after the commit succeeds. Verify during implementation: if the API process dies between commit and in-memory release, the next process restart must rebuild the capacity counter from the DB. If that reconciliation isn't already in place, this spec needs a follow-up note; flagged as an implementation-time check.

**Response body** gains `refunded_credits: u32` (replacing the old `refunded: bool`):

```json
{ "cancelled": true, "refunded_credits": 3 }
```

The SSE `JobEvent::Cancelled` payload gains the same field so subscribers see the refund alongside the state change.

## UI surface

`/research` → `NewJobForm` in `nasrudin-frontend/src/routes/research.tsx`.

Two new controls between the domain-hint dropdown and the submit button:

```
[hunch textarea]
[domain hint dropdown]

──────────────────────────────────
Effort                    Credits
[●━━━━━━━━━━━━━━━━━━━━]      3
1 credit (96 slot-h)         max
3 credits = 288 slot-hours of cluster time
≈ 4 slots × 72 hours, or 12 slots × 24 hours

[ ] Rush  +1 credit, jumps your job
         ahead of normal-priority work

──────────────────────────────────
Total: 4 credits  ·  6 remaining
[ Submit (4 credits) ]
```

**State:**

```ts
const [creditsBudget, setCreditsBudget] = useState(1);
const [rush, setRush] = useState(false);
const me = useMe();
const remaining = me.data?.research_credits_remaining ?? 0;
const totalCost = creditsBudget + (rush ? 1 : 0);
const canSubmit = hunch.trim().length > 0 && totalCost <= remaining && totalCost >= 1;
```

**Slider:** `<input type="range" min={1} max={Math.max(1, remaining - (rush ? 1 : 0))} step={1}>`. The dynamic max shrinks by 1 when rush is on so the user can't pick budget=remaining + rush=on and bounce off 402. Symmetric: rush is disabled when `creditsBudget === remaining`.

**Live readout:** below the slider, recompute `slot_hours = creditsBudget × 96` on every change. Show both forms ("288 slot-hours" and "4 slots × 72 hours") so users can map onto wallclock.

**Submit button:** label updates from `Submit (1 credit)` to `Submit (N credits)` reflecting `totalCost`.

**Empty wallet:** when `remaining === 0`, the slider+rush block is replaced with an inline upgrade prompt (link to `/pricing`). Submit hard-disabled. Clearer signal than greyed-out widgets.

**402 race recovery:** the catch block writes the fresh `remaining` from the response body back into the `me` query cache so subsequent renders show accurate state:

```ts
catch (e) {
  if (isApiError(e) && e.status === 402 && typeof e.body?.remaining === 'number') {
    qc.setQueryData(meProfileQueryKey, (old: Me | undefined) =>
      old ? { ...old, research_credits_remaining: e.body.remaining } : old
    );
    setError(`Need ${e.body.required} credits, you have ${e.body.remaining}.`);
  }
}
```

**Slider re-clamp on remaining drop:** `useEffect` watches `remaining` and `rush`; if the current `creditsBudget` exceeds `remaining - (rush ? 1 : 0)`, clamp it down. If `rush` is on and `remaining < 2`, force `rush` off.

**Job row display** (`JobRow`): the existing "X / Y slot-h (Z%)" line keeps working unchanged — `lake_slot_hours_quota` reflects the chosen budget. Add a small `RUSH` chip next to the state badge when `slice_priority > 5`.

**Cancel confirmation copy:** updated to match the new proportional rule:

> Cancel this conjecture? If no theorems were verified, you'll be refunded credits proportional to the unused budget.

The cancel mutation's `onSuccess` reads `refunded_credits` from the response and surfaces it in the toast: "Cancelled. Refunded 3 credits." or "Cancelled. No refund (work was completed)."

## Error handling

| Failure | Caught | Response |
|---|---|---|
| `credits_budget < 1` | API handler validation | `400 invalid_credits_budget` |
| `credits_budget` overflow / non-numeric | serde deserialize | 400 with serde's default error |
| User has fewer than `n` credits | `UPDATE ... WHERE remaining >= $n` returns 0 rows | `402 insufficient_research_credits` with `{required, remaining}` |
| Concurrent submit drains credits | Same path | UI updates `me` cache from response body |
| Job-row insert fails (constraint/connection) | Transaction rollback | 500; credit auto-restored by rollback |
| Cancel on already-terminal job | Conditional UPDATE returns 0 rows | `409 terminal_state` |
| Double-clicked cancel | Same — second call hits 409 | UI shows no toast (idempotent) |
| Heartbeat lands after cancel | Heartbeat's `WHERE state IN ('claimed','running')` no-ops | Silent (verify path) |
| Worker dies mid-job | Existing lease-expiry tick reaps stale claims | Job returns to `queued`; credits stay debited |
| `consumed > quota` (lying worker) | `GREATEST(0.0, ...)` clamps | Refund = 0 |
| `quota = 0` div-by-zero | Can't happen (`credits_budget ≥ 1`) | N/A |

**Logging:** structured log lines at the two decision points — `submit_decremented user=… credits=… job=…` and `cancel_refunded user=… job=… refund=…`.

## Backwards compatibility

- Existing callers that POST `{hunch, domain_hint}` continue to work unchanged: defaults `credits_budget=1, rush=false` reproduce today's exact behavior (96 slot-h, priority 5, 1 credit cost).
- Existing rows have `lake_slot_hours_quota=96` and `slice_priority=5`, so cancel's reconstructed `credits_spent` is `(96/96) + 0 = 1`, which is correct.
- The `refunded` boolean in the cancel response is replaced with `refunded_credits: u32`. This is a breaking response shape but the only frontend consumer is `useCancelResearchJob`'s success handler, which we update in the same change.

## Testing

**Backend unit:**
- `try_decrement_research_credits_n` with `n` greater than, equal to, and less than remaining.
- Transaction rollback on insert failure leaves credits intact.
- Cancel with `verified == 0`, various `consumed/quota` ratios — refund is `floor(credits × (1 - ratio))`.
- Cancel with `verified > 0` — refund is 0 regardless of ratio.
- Cancel with `consumed > quota` — refund clamps to 0.
- Cancel on `proved` / already-`cancelled` row — returns 0 affected rows; no refund.
- Concurrent cancels from two requests — one gets 200, other gets 409; refund applied exactly once.

**Backend integration:**
- Two parallel POSTs from same user, both requesting `n` credits when only `n` are available — exactly one succeeds; loser sees 402 with `remaining: 0`.
- POST with `credits_budget: 0` → 400.
- POST with `rush: true` and only 1 credit remaining → 402.
- POST with `credits_budget: 5` and 10 credits remaining → row created with `lake_slot_hours_quota: 480, slice_priority: 5`, user has 5 credits left.
- POST with `credits_budget: 5, rush: true` → row created with `quota: 480, slice_priority: 6`; user has 4 credits left.

**Frontend:**
- Slider clamp: when `remaining` drops below current value via `me` refetch, slider value clamps down.
- Rush disabled when `remaining === 1` and budget at max.
- Empty-wallet view replaces the slider/rush block with an upgrade prompt.
- 402 race: server returns `{required: 6, remaining: 4}`, query cache updates, error message displays correctly.
- `JobRow` shows the `RUSH` chip when `slice_priority > 5`, hides it otherwise.
- Cancel toast shows `refunded_credits` count.

## Open implementation-time verifications

These need to be confirmed when writing the plan / writing code, not now:

1. **Heartbeat WHERE clause includes state guard.** The cancel race-safety argument assumes `UPDATE conjecture_jobs SET lake_slot_hours_consumed = ... WHERE id = ? AND state IN ('claimed','running')`. If the existing heartbeat path doesn't include the state filter, add it.
2. **Capacity counter rebuilds from DB on API restart.** The slot-pool release happens outside the cancel transaction. If the API can crash between commit and in-memory release, the rebuild path must reconcile from `conjecture_jobs` rows in non-terminal states. If no such rebuild exists today, this spec needs a follow-up.
3. **`/api/me` exposes `research_credits_remaining`.** The frontend slider depends on it. Quick grep confirms the field exists on `users`; verify the `me` handler surfaces it.

These are listed for the planning phase to investigate; none change the design.

## Out of scope

- Mid-flight top-up of a queued/running job (Q4 = A; deferred).
- Stepped rush dial / multi-level priority bumps (Q3b = i).
- Dropping the credits abstraction in favour of a slot-hour pool per user (Q1 option C; rejected).
- Pricing-page copy changes. The pricing page promises "1 credit = 1 paid conjecture, 96 slot-hours each"; the new model still reads as truthful (each credit still buys 96 slot-h; one conjecture can now stack credits). A follow-up copy review may be warranted but is not blocked by this spec.
