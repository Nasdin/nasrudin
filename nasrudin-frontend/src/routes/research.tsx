import { useQueryClient } from '@tanstack/react-query';
import { createFileRoute, useNavigate } from '@tanstack/react-router';
import { type FormEvent, useEffect, useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { SignInPrompt } from '~/components/platform/SignInPrompt';
import { isApiError } from '~/lib/api';
import {
  meQueryKey,
  useCancelResearchJob,
  useCreateResearchJob,
  useMe,
  useResearchJobs,
} from '~/lib/queries';
import type { AuthUser, ResearchJob } from '~/lib/types';

export const Route = createFileRoute('/research')({ component: ResearchPage });

function ResearchPage() {
  const me = useMe();
  const list = useResearchJobs();
  if (me.isPending) return null;
  if (!me.data)
    return (
      <SignInPrompt
        active="research"
        overline="Researcher tier — $19/mo"
        title="Paid conjectures"
        description="Hand the system a conjecture you can't prove and a slice of the GA cluster tries to evolve a Lean 4 proof of it. Sign in to start a run."
      />
    );

  return (
    <div className="app">
      <AppHeader active="research" />
      <div className="container-wide" style={{ maxWidth: 880 }}>
        <div className="page-head">
          <span className="overline">Researcher tier — $19/mo</span>
          <h1>
            Paid conjectures —{' '}
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              point the cluster at one specific theorem.
            </em>
          </h1>
          <p className="lede">
            Hand the system a conjecture you can't prove. A slice of the GA cluster (4 lake slots ×
            24 h = 96 slot-hours) tries to evolve a Lean 4 proof of it. One credit per conjecture;
            10 credits per billing period.
          </p>
        </div>

        <NewJobForm />

        <section style={{ marginTop: 48 }}>
          <h2 style={{ fontSize: 18, marginBottom: 12 }}>Your conjectures</h2>
          {list.isPending && <p className="hint">Loading…</p>}
          {list.error && (
            <p className="hint" role="alert">
              Couldn't load: {String(list.error)}
            </p>
          )}
          {list.data && list.data.jobs.length === 0 && (
            <p className="hint">No paid conjectures yet. Submit one above.</p>
          )}
          {list.data && list.data.jobs.length > 0 && (
            <ul style={{ listStyle: 'none', padding: 0, margin: 0 }}>
              {list.data.jobs.map((j) => (
                <JobRow key={j.id} job={j} />
              ))}
            </ul>
          )}
        </section>
      </div>
      <AppFooter />
    </div>
  );
}

function NewJobForm() {
  const create = useCreateResearchJob();
  const navigate = useNavigate();
  const qc = useQueryClient();
  const me = useMe();
  const [hunch, setHunch] = useState('');
  const [domainHint, setDomainHint] = useState('');
  const [creditsBudget, setCreditsBudget] = useState(1);
  const [rush, setRush] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const remaining = me.data?.research_credits ?? 0;
  const totalCost = creditsBudget + (rush ? 1 : 0);
  const slotHours = creditsBudget * 96;

  // Re-clamp the slider when remaining drops (e.g. another tab spent
  // credits) or the rush toggle flips. Keeps the UI consistent with
  // the wallet view returned by /api/auth/me.
  useEffect(() => {
    const cap = Math.max(1, remaining - (rush ? 1 : 0));
    if (creditsBudget > cap) setCreditsBudget(cap);
    if (rush && remaining < 2) setRush(false);
  }, [remaining, rush, creditsBudget]);

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    try {
      const res = await create.mutateAsync({
        hunch: hunch.trim(),
        domain_hint: domainHint.trim() || null,
        credits_budget: creditsBudget,
        rush,
      });
      navigate({ to: '/research/$id', params: { id: res.job_id } });
    } catch (e) {
      if (isApiError(e)) {
        if (
          e.status === 402 &&
          e.body &&
          typeof e.body === 'object' &&
          'remaining' in e.body
        ) {
          // Backend told us the truth — sync the cache so the slider's
          // useEffect re-clamps on next render.
          const body = e.body as Record<string, unknown>;
          const fresh = Number(body.remaining ?? 0);
          const required = Number(body.required ?? totalCost);
          qc.setQueryData(meQueryKey, (old: AuthUser | null | undefined) =>
            old ? { ...old, research_credits: fresh } : old,
          );
          setError(`Need ${required} credit${required === 1 ? '' : 's'}, you have ${fresh}.`);
        } else if (e.body && typeof e.body === 'object' && 'error' in e.body) {
          setError(String((e.body as { error: unknown }).error));
        } else {
          setError(`Request failed (${e.status})`);
        }
      } else {
        setError('Network error');
      }
    }
  }

  const submitDisabled =
    create.isPending ||
    hunch.trim().length === 0 ||
    totalCost > remaining ||
    remaining === 0;

  const sliderMax = Math.max(1, remaining - (rush ? 1 : 0));
  const rushDisabled = !rush && remaining - creditsBudget < 1;

  return (
    <form onSubmit={onSubmit} style={{ maxWidth: 640, marginTop: 32 }}>
      <div className="field">
        <label htmlFor="hunch">Conjecture</label>
        <textarea
          id="hunch"
          value={hunch}
          onChange={(e) => setHunch(e.target.value)}
          rows={5}
          required
          placeholder="E = m c^2"
          style={{
            background: 'var(--bg-raised)',
            border: '1px solid var(--paper-200)',
            borderRadius: 'var(--radius-md)',
            padding: '12px 14px',
            fontFamily: 'var(--font-mono)',
            fontSize: 15,
            color: 'var(--ink-900)',
            resize: 'vertical',
          }}
        />
        <span className="hint">
          LaTeX preferred — the runner compiles it into a canonical-form hash and marks the job{' '}
          <code>proved</code> when a kernel-verified theorem matches. Plain English works too but
          disables exact-match checking; the runner falls back to "first kernel-verified theorem in
          the slice is the proof" and your refund eligibility depends on whether it produced any
          verified results.
        </span>
      </div>

      <div className="field">
        <label htmlFor="domain">Domain hint (optional)</label>
        <select id="domain" value={domainHint} onChange={(e) => setDomainHint(e.target.value)}>
          <option value="">—</option>
          <option value="special_relativity">Special Relativity</option>
          <option value="electromagnetism">Electromagnetism</option>
          <option value="classical_mechanics">Classical Mechanics</option>
          <option value="thermodynamics">Thermodynamics</option>
          <option value="quantum_mechanics">Quantum Mechanics</option>
          <option value="general_relativity">General Relativity</option>
          <option value="pure_math">Pure Math</option>
        </select>
        <span className="hint">
          Steers the explorer fleet's bias toward prerequisite lemmas in the relevant domain.
        </span>
      </div>

      {remaining === 0 ? (
        <div
          className="hint"
          style={{
            marginTop: 24,
            padding: 12,
            border: '1px solid var(--paper-200)',
            borderRadius: 'var(--radius-md)',
            background: 'var(--bg-raised)',
          }}
        >
          0 credits available. Wait for renewal or <a href="/pricing">upgrade your plan</a>.
        </div>
      ) : (
        <div className="field" style={{ marginTop: 24 }}>
          <div
            style={{
              display: 'flex',
              justifyContent: 'space-between',
              alignItems: 'baseline',
            }}
          >
            <label htmlFor="credits-budget">Effort</label>
            <span style={{ fontFamily: 'var(--font-mono)', fontSize: 13 }}>
              {creditsBudget} credit{creditsBudget === 1 ? '' : 's'}
            </span>
          </div>
          <input
            id="credits-budget"
            type="range"
            min={1}
            max={sliderMax}
            step={1}
            value={creditsBudget}
            onChange={(e) => setCreditsBudget(Number(e.target.value))}
            style={{ width: '100%', marginTop: 8 }}
          />
          <span className="hint">
            {slotHours} lake-slot-hours of cluster time · ≈ 4 slots × {slotHours / 4} h, or 12 slots
            × {(slotHours / 12).toFixed(1)} h
          </span>

          <label
            style={{
              display: 'flex',
              alignItems: 'center',
              gap: 8,
              marginTop: 16,
              fontSize: 14,
              color: rushDisabled ? 'var(--ink-500)' : 'var(--ink-900)',
            }}
          >
            <input
              type="checkbox"
              checked={rush}
              disabled={rushDisabled}
              onChange={(e) => setRush(e.target.checked)}
            />
            <span>
              <strong>Rush</strong> — +1 credit, jumps your job ahead of normal-priority work
            </span>
          </label>

          <div
            style={{
              marginTop: 16,
              display: 'flex',
              justifyContent: 'space-between',
              fontSize: 13,
              color: 'var(--ink-600)',
            }}
          >
            <span>
              Total: <strong>{totalCost}</strong> credit{totalCost === 1 ? '' : 's'}
            </span>
            <span>{remaining} remaining</span>
          </div>
        </div>
      )}

      {error && (
        <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginTop: 12 }}>
          {error}
        </div>
      )}

      <div style={{ marginTop: 24 }}>
        <button type="submit" className="btn btn-primary" disabled={submitDisabled}>
          {create.isPending
            ? 'Submitting…'
            : `Submit (${totalCost} credit${totalCost === 1 ? '' : 's'})`}
        </button>
      </div>
    </form>
  );
}

function JobRow({ job }: { job: ResearchJob }) {
  const cancel = useCancelResearchJob();
  const terminal = ['proved', 'budget_exhausted', 'cancelled', 'Complete'];
  const isTerminal = terminal.includes(job.state);
  const isRush = job.slice_priority > 5;
  const slotPct = Math.min(
    100,
    Math.round((job.lake_slot_hours_consumed / job.lake_slot_hours_quota) * 100),
  );

  return (
    <li
      style={{
        padding: 16,
        marginBottom: 12,
        background: 'var(--bg-raised)',
        border: '1px solid var(--paper-200)',
        borderRadius: 'var(--radius-md)',
      }}
    >
      <div
        style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'baseline',
          gap: 12,
          flexWrap: 'wrap',
        }}
      >
        <a href={`/research/${job.id}`} style={{ fontFamily: 'var(--font-mono)', fontSize: 14 }}>
          {job.hunch.slice(0, 80)}
          {job.hunch.length > 80 && '…'}
        </a>
        <div style={{ display: 'flex', gap: 6 }}>
          {isRush && <RushChip />}
          <StateBadge state={job.state} />
        </div>
      </div>
      <div
        style={{
          marginTop: 8,
          display: 'flex',
          gap: 16,
          flexWrap: 'wrap',
          fontSize: 12,
          color: 'var(--ink-600)',
        }}
      >
        <span>
          {job.candidates_verified.toLocaleString()} verified ·{' '}
          {job.candidates_attempted.toLocaleString()} tried
        </span>
        <span>
          {job.lake_slot_hours_consumed.toFixed(1)} / {job.lake_slot_hours_quota} slot-h ({slotPct}
          %)
        </span>
        <span>{new Date(job.created_at).toLocaleDateString()}</span>
      </div>
      {!isTerminal && (
        <div style={{ marginTop: 12 }}>
          <button
            type="button"
            className="btn btn-secondary"
            disabled={cancel.isPending}
            onClick={() => {
              if (
                confirm(
                  "Cancel this conjecture? If no theorems were verified, you'll be refunded credits proportional to the unused budget.",
                )
              ) {
                cancel
                  .mutateAsync(job.id)
                  .then((r) => {
                    if (r.refunded_credits > 0) {
                      alert(
                        `Cancelled. Refunded ${r.refunded_credits} credit${r.refunded_credits === 1 ? '' : 's'}.`,
                      );
                    } else {
                      alert('Cancelled. No refund (work was completed or in-flight).');
                    }
                  })
                  .catch(() => {
                    /* mutation error already surfaced via cancel.error */
                  });
              }
            }}
          >
            {cancel.isPending ? 'Cancelling…' : 'Cancel'}
          </button>
        </div>
      )}
    </li>
  );
}

function RushChip() {
  return (
    <span
      style={{
        fontSize: 11,
        textTransform: 'uppercase',
        letterSpacing: 0.5,
        padding: '4px 8px',
        borderRadius: 'var(--radius-sm)',
        background: 'var(--terracotta-100, var(--paper-300))',
        color: 'var(--terracotta-700, var(--ink-700))',
      }}
    >
      Rush
    </span>
  );
}

function StateBadge({ state }: { state: string }) {
  const palette: Record<string, { bg: string; fg: string }> = {
    queued: { bg: 'var(--paper-200)', fg: 'var(--ink-700)' },
    claimed: { bg: 'var(--blue-100)', fg: 'var(--blue-700)' },
    running: { bg: 'var(--blue-100)', fg: 'var(--blue-700)' },
    proved: { bg: 'var(--success-100)', fg: 'var(--success-700)' },
    budget_exhausted: { bg: 'var(--paper-300)', fg: 'var(--ink-600)' },
    cancelled: { bg: 'var(--paper-200)', fg: 'var(--ink-500)' },
  };
  const c = palette[state] ?? { bg: 'var(--paper-200)', fg: 'var(--ink-700)' };
  return (
    <span
      style={{
        fontSize: 11,
        textTransform: 'uppercase',
        letterSpacing: 0.5,
        padding: '4px 8px',
        borderRadius: 'var(--radius-sm)',
        background: c.bg,
        color: c.fg,
      }}
    >
      {state}
    </span>
  );
}
