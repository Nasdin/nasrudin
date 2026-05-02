import { createFileRoute, Link } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { SignInPrompt } from '~/components/platform/SignInPrompt';
import { useMe, useMyConjectures } from '~/lib/queries';

export const Route = createFileRoute('/jobs')({ component: JobsPage });

function JobsPage() {
  const me = useMe();
  const list = useMyConjectures();

  if (me.isPending) return null;
  if (!me.data)
    return (
      <SignInPrompt
        active="conjecture"
        overline="Research"
        title="Your conjectures"
        description="Hypotheses you've sent through the loop will live here once you sign in."
      />
    );

  return (
    <div className="app">
      <AppHeader active="conjecture" />
      <div className="container-wide" style={{ maxWidth: 980 }}>
        <div className="page-head">
          <span className="overline">Research</span>
          <h1>
            Your conjectures —{' '}
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              hypotheses you've sent through the loop.
            </em>
          </h1>
        </div>
        <div className="page-body">
          {list.isPending && <div>Loading…</div>}
          {list.data && list.data.conjectures.length === 0 && (
            <div className="card">
              No conjectures yet.{' '}
              <Link to="/conjecture">Submit your first one →</Link>
            </div>
          )}
          {list.data && list.data.conjectures.length > 0 && (
            <ul style={{ listStyle: 'none', padding: 0, margin: 0 }}>
              {list.data.conjectures.map((c) => (
                <li key={c.id} className="jobs-row">
                  <span className="jobs-row-date">
                    {new Date(c.created_at).toLocaleString()}
                  </span>
                  <Link
                    to="/conjecture/$id"
                    params={{ id: c.id }}
                    className="jobs-row-link"
                  >
                    {c.hunch.slice(0, 100)}
                    {c.hunch.length > 100 ? '…' : ''}
                  </Link>
                  <StatePill state={c.state} outcome={c.outcome} />
                </li>
              ))}
            </ul>
          )}
        </div>
      </div>
      <AppFooter />
    </div>
  );
}

function StatePill({ state, outcome }: { state: string; outcome: string | null }) {
  const text = state === 'Complete' && outcome ? `Complete · ${outcome}` : state;
  const bg =
    state === 'Complete'
      ? 'var(--olive-100)'
      : state === 'Running'
      ? 'var(--terracotta-100)'
      : 'var(--paper-100)';
  return (
    <span
      style={{
        fontFamily: 'var(--font-mono)',
        fontSize: 12,
        padding: '2px 10px',
        borderRadius: 999,
        background: bg,
        color: 'var(--ink-700)',
      }}
    >
      {text}
    </span>
  );
}
