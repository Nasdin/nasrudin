import { createFileRoute, Link, redirect } from '@tanstack/react-router';
import { useState } from 'react';
import { JobProgress } from '~/components/conjecture/JobProgress';
import { SuggestionCard } from '~/components/conjecture/SuggestionCard';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { isApiError } from '~/lib/api';
import {
  useConjecture,
  useConjectureStream,
  useMe,
  useStartConjecture,
} from '~/lib/queries';

export const Route = createFileRoute('/conjecture/$id')({ component: ConjectureJobPage });

function ConjectureJobPage() {
  const { id } = Route.useParams();
  const me = useMe();
  const job = useConjecture(id);
  const start = useStartConjecture(id);
  const liveEvents = useConjectureStream(id);
  const [chosen, setChosen] = useState<number | null>(null);
  const [startError, setStartError] = useState<string | null>(null);

  if (me.isPending || job.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });
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
      </div>
      <AppFooter />
    </div>
  );
}
