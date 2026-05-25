import { createFileRoute, Link } from '@tanstack/react-router';
import { useState } from 'react';
import { JobProgress } from '~/components/conjecture/JobProgress';
import { SuggestionCard } from '~/components/conjecture/SuggestionCard';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { SignInPrompt } from '~/components/platform/SignInPrompt';
import { isApiError } from '~/lib/api';
import { API_BASE } from '~/lib/api';
import {
  useConjecture,
  useConjectureStream,
  useMe,
  useStartConjecture,
  useStartPaperDraft,
} from '~/lib/queries';

export const Route = createFileRoute('/conjecture/$id')({ loader: async () => null, component: ConjectureJobPage });

function ConjectureJobPage() {
  const { id } = Route.useParams();
  const me = useMe();
  const job = useConjecture(id);
  const start = useStartConjecture(id);
  const liveEvents = useConjectureStream(id);
  const [chosen, setChosen] = useState<number | null>(null);
  const [startError, setStartError] = useState<string | null>(null);

  if (me.isPending || job.isPending) return null;
  if (!me.data)
    return (
      <SignInPrompt
        active="conjecture"
        overline="Research"
        title="Conjecture"
        description="Conjecture runs are private to the user that submitted them. Sign in to view this run."
      />
    );
  if (!job.data) {
    return (
      <div className="app">
        <AppHeader active="conjecture" />
        <div className="container-wide">
          <p>Conjecture not found.</p>
        </div>
        <AppFooter />
      </div>
    );
  }

  const view = job.data;
  const canChoose = view.state === 'LlmComplete' && view.suggestions != null;
  const isLive = ['QueuedForWorker', 'Running', 'Complete'].includes(view.state);

  async function onStart() {
    if (chosen == null) return;
    setStartError(null);
    try {
      await start.mutateAsync({ chosen_index: chosen });
    } catch (e) {
      if (isApiError(e)) {
        const body =
          e.body && typeof e.body === 'object' && 'error' in e.body
            ? String((e.body as { error: unknown }).error)
            : `Request failed (${e.status})`;
        setStartError(body);
      } else {
        setStartError('Network error');
      }
    }
  }

  return (
    <div className="app">
      <AppHeader active="conjecture" />
      <div className="container-wide" style={{ maxWidth: 880 }}>
        <div className="page-head">
          <span className="overline">Conjecture · {view.state}</span>
          <h1>
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              {view.hunch}
            </em>
          </h1>
          <p className="lede">
            {view.provider} / {view.model} · budget {view.budget.wall_seconds}s ·{' '}
            {view.budget.max_candidates.toLocaleString()} candidates
          </p>
        </div>

        {canChoose && view.suggestions && (
          <div className="page-body">
            <h3 className="section-h" style={{ fontSize: 22, marginBottom: 16 }}>
              LLM suggestions
            </h3>
            {view.suggestions.map((s, i) => (
              <SuggestionCard
                key={i}
                suggestion={s}
                index={i}
                selected={chosen === i}
                onSelect={() => setChosen(i)}
              />
            ))}
            {startError && (
              <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13 }}>
                {startError}
              </div>
            )}
            <div style={{ marginTop: 16, display: 'flex', gap: 12 }}>
              <button
                type="button"
                className="btn btn-primary"
                disabled={chosen == null || start.isPending}
                onClick={onStart}
              >
                {start.isPending ? 'Queuing…' : 'Start GA run'}
              </button>
            </div>
          </div>
        )}

        {isLive && <JobProgress view={view} events={liveEvents} />}

        {view.state === 'Complete' && view.verified_theorem_ids.length > 0 && (
          <div className="card" style={{ marginTop: 24 }}>
            <h3 className="section-h" style={{ fontSize: 22, marginBottom: 16 }}>
              Verified theorems
            </h3>
            <ul style={{ listStyle: 'none', padding: 0, margin: 0 }}>
              {view.verified_theorem_ids.map((tid) => (
                <li key={tid} style={{ fontFamily: 'var(--font-mono)', padding: '4px 0' }}>
                  <Link to="/theorem/$id" params={{ id: tid }}>
                    {tid}
                  </Link>
                </li>
              ))}
            </ul>
          </div>
        )}

        {view.state === 'Complete' && view.outcome === 'Verified' && (
          <PaperDraftSection id={id} events={liveEvents} />
        )}
      </div>
      <AppFooter />
    </div>
  );
}

function PaperDraftSection({
  id,
  events,
}: {
  id: string;
  events: import('~/lib/types').ConjectureSseEvent[];
}) {
  const start = useStartPaperDraft(id);
  // Reconstruct the live draft from paper_chunk events arriving on SSE.
  const liveDraft = events
    .filter((e) => e.kind === 'paper_chunk')
    .map((e) => {
      const p = e.payload as { text?: string };
      return p?.text ?? '';
    })
    .join('');
  const isStreaming =
    events.some((e) => e.kind === 'paper_chunk') &&
    !events.some((e) => e.kind === 'paper_done' || e.kind === 'paper_error');
  const errorEvent = events.find((e) => e.kind === 'paper_error');

  return (
    <div className="card" style={{ marginTop: 24 }}>
      <div
        style={{
          display: 'flex',
          alignItems: 'baseline',
          justifyContent: 'space-between',
          marginBottom: 16,
        }}
      >
        <h3 className="section-h" style={{ fontSize: 22, margin: 0 }}>
          Paper draft
        </h3>
        <div style={{ display: 'flex', gap: 12 }}>
          <a
            href={`${API_BASE}/api/conjecture/${id}/paper.md`}
            download={`conjecture-${id}.md`}
            className="btn btn-secondary"
            style={{ fontSize: 13 }}
          >
            Download .md
          </a>
          <button
            type="button"
            className="btn btn-primary"
            onClick={() => start.mutate()}
            disabled={start.isPending || isStreaming}
          >
            {start.isPending || isStreaming ? 'Generating…' : 'Generate draft'}
          </button>
        </div>
      </div>
      {errorEvent && (
        <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginBottom: 12 }}>
          Stream error:{' '}
          {(errorEvent.payload as { error?: string })?.error ?? 'unknown'}
        </div>
      )}
      {liveDraft.length > 0 ? (
        <pre
          style={{
            whiteSpace: 'pre-wrap',
            fontFamily: 'var(--font-mono)',
            fontSize: 13,
            color: 'var(--ink-900)',
            background: 'var(--bg-raised)',
            padding: 16,
            borderRadius: 'var(--radius-md)',
            border: '1px solid var(--paper-200)',
            maxHeight: 480,
            overflowY: 'auto',
          }}
        >
          {liveDraft}
        </pre>
      ) : (
        <div style={{ color: 'var(--ink-500)', fontSize: 13 }}>
          {start.isPending
            ? 'Calling LLM…'
            : 'Click "Generate draft" to ask the same provider that proposed the conjecture to write a 1-2 page Markdown paper from the verified theorems.'}
        </div>
      )}
    </div>
  );
}
