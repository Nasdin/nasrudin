import { createFileRoute, redirect } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useCancelResearchJob, useMe, useResearchJob, useResearchJobStream } from '~/lib/queries';
import type { ResearchJob, ResearchJobEvent } from '~/lib/types';

export const Route = createFileRoute('/research/$id')({ component: ResearchDetailPage });

function ResearchDetailPage() {
  const me = useMe();
  const { id } = Route.useParams();
  const job = useResearchJob(id);
  const events = useResearchJobStream(id);
  const cancel = useCancelResearchJob();

  if (me.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });

  return (
    <div className="app">
      <AppHeader active="research" />
      <div className="container-wide" style={{ maxWidth: 880 }}>
        <div className="page-head">
          <span className="overline">Paid conjecture</span>
          <h1 style={{ fontFamily: 'var(--font-mono)', fontSize: 22 }}>
            {job.data ? job.data.hunch.slice(0, 120) : id.slice(0, 8)}
          </h1>
          <p className="lede">
            Live progress streamed from the worker handling this conjecture. The page auto-updates;
            no refresh needed.
          </p>
        </div>

        {job.isPending && <p className="hint">Loading…</p>}
        {job.error && (
          <p role="alert" style={{ color: 'var(--danger-500)' }}>
            {String(job.error)}
          </p>
        )}
        {job.data && <Detail job={job.data} events={events} />}

        {job.data && !isTerminal(job.data.state) && (
          <div style={{ marginTop: 24 }}>
            <button
              type="button"
              className="btn btn-secondary"
              disabled={cancel.isPending}
              onClick={() => {
                if (
                  confirm(
                    'Cancel this conjecture? You may get a refund if no theorems were verified yet.',
                  )
                ) {
                  cancel.mutate(id);
                }
              }}
            >
              {cancel.isPending ? 'Cancelling…' : 'Cancel'}
            </button>
          </div>
        )}
      </div>
      <AppFooter />
    </div>
  );
}

function isTerminal(state: string): boolean {
  return ['proved', 'budget_exhausted', 'cancelled', 'Complete'].includes(state);
}

function Detail({ job, events }: { job: ResearchJob; events: ResearchJobEvent[] }) {
  const slotPct = Math.min(
    100,
    Math.round((job.lake_slot_hours_consumed / job.lake_slot_hours_quota) * 100),
  );

  // Aggregate the latest progress numbers across SSE events. The
  // Progress event carries deltas relative to the last heartbeat;
  // we show the cumulative numbers from the row + best chain stats
  // from the most recent Progress event for live "what's the GA up to
  // right now" feedback.
  const lastProgress = events
    .slice()
    .reverse()
    .find((e): e is Extract<ResearchJobEvent, { kind: 'progress' }> => e.kind === 'progress');
  const provedEv = events.find(
    (e): e is Extract<ResearchJobEvent, { kind: 'proved' }> => e.kind === 'proved',
  );

  return (
    <div className="page-body">
      <section
        style={{
          padding: 16,
          background: 'var(--bg-raised)',
          border: '1px solid var(--paper-200)',
          borderRadius: 'var(--radius-md)',
        }}
      >
        <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
          <h2 style={{ fontSize: 16, margin: 0 }}>State</h2>
          <span style={{ fontSize: 14, fontWeight: 600 }}>{job.state}</span>
        </div>
        <p className="hint" style={{ marginTop: 4 }}>
          Created {new Date(job.created_at).toLocaleString()}
          {job.completed_at && ` · Completed ${new Date(job.completed_at).toLocaleString()}`}
        </p>
      </section>

      <section style={{ marginTop: 24 }}>
        <h2 style={{ fontSize: 16 }}>Budget</h2>
        <div style={{ display: 'flex', alignItems: 'center', gap: 12 }}>
          <progress value={slotPct} max={100} style={{ width: '100%' }} />
          <span style={{ fontSize: 13, fontVariantNumeric: 'tabular-nums', minWidth: 120 }}>
            {job.lake_slot_hours_consumed.toFixed(1)} / {job.lake_slot_hours_quota} slot-h
          </span>
        </div>
      </section>

      <section style={{ marginTop: 24 }}>
        <h2 style={{ fontSize: 16 }}>Progress</h2>
        <ul style={{ listStyle: 'none', padding: 0, fontSize: 13, color: 'var(--ink-600)' }}>
          <li>Candidates attempted: {job.candidates_attempted.toLocaleString()}</li>
          <li>Candidates verified: {job.candidates_verified.toLocaleString()}</li>
          {lastProgress && (
            <>
              <li>Best chain length: {lastProgress.best_chain_length}</li>
              <li>Best fitness: {lastProgress.best_fitness.toFixed(3)}</li>
            </>
          )}
        </ul>
      </section>

      {provedEv && (
        <section
          style={{
            marginTop: 24,
            padding: 16,
            background: 'var(--success-50, var(--paper-200))',
            border: '1px solid var(--success-200, var(--paper-300))',
            borderRadius: 'var(--radius-md)',
          }}
        >
          <h2 style={{ fontSize: 16, margin: 0 }}>Proved</h2>
          <p style={{ marginTop: 8 }}>
            <a href={provedEv.lean_url}>Download the Lean source</a>
          </p>
        </section>
      )}

      <section style={{ marginTop: 24 }}>
        <h2 style={{ fontSize: 16 }}>Live event log</h2>
        {events.length === 0 ? (
          <p className="hint">Waiting for a worker to claim this conjecture…</p>
        ) : (
          <ol
            style={{
              listStyle: 'none',
              padding: 0,
              fontFamily: 'var(--font-mono)',
              fontSize: 12,
              maxHeight: 320,
              overflow: 'auto',
              border: '1px solid var(--paper-200)',
              borderRadius: 'var(--radius-md)',
              background: 'var(--bg-raised)',
            }}
          >
            {events
              .slice()
              .reverse()
              .map((e, i) => {
                // Append-only event log — events never reorder, so
                // (length-1-i) is a stable identity even though it's
                // a positional key. Compose with `kind` so React treats
                // sibling-shape changes as a re-render rather than a
                // remount.
                const key = `${events.length - 1 - i}-${e.kind}`;
                return (
                  <li
                    key={key}
                    style={{
                      padding: '6px 12px',
                      borderBottom: '1px solid var(--paper-100)',
                    }}
                  >
                    <strong>{e.kind}</strong>{' '}
                    <span style={{ color: 'var(--ink-500)' }}>{summarise(e)}</span>
                  </li>
                );
              })}
          </ol>
        )}
      </section>
    </div>
  );
}

function summarise(e: ResearchJobEvent): string {
  switch (e.kind) {
    case 'job_state':
      return `→ ${e.state}`;
    case 'progress':
      return `+${e.candidates_attempted} tried, +${e.candidates_verified} verified, ${e.lake_slot_hours_consumed.toFixed(2)}h consumed`;
    case 'theorem_verified':
      return `${e.theorem_id_hex.slice(0, 12)}… : ${e.statement_latex.slice(0, 60)}`;
    case 'proved':
      return e.lean_url;
    case 'budget_exhausted':
      return `${e.best_partial_summary} (refund ${e.refund_credits})`;
    case 'cancelled':
      return '';
  }
}
