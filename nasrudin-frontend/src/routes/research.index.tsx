import { useQueryClient } from '@tanstack/react-query';
import { createFileRoute, useNavigate } from '@tanstack/react-router';
import { type FormEvent, useEffect, useMemo, useState } from 'react';
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
  useSteeringOptions,
} from '~/lib/queries';
import {
  buildSteeringPayload,
  emptySteeringForm,
  hasAnySteering,
  prettyDomainKey,
  prettyOperatorName,
  type SteeringFormState,
} from '~/lib/steering';
import type { AuthUser, ResearchJob, SteeringOptions } from '~/lib/types';

export const Route = createFileRoute('/research/')({
  loader: async () => null,
  component: ResearchPage,
});

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
  const [advancedOpen, setAdvancedOpen] = useState(false);
  const [steering, setSteering] = useState<SteeringFormState>(emptySteeringForm);
  const [error, setError] = useState<string | null>(null);

  // Only fetch the options metadata once the user actually opens the
  // disclosure; on the typical "submit a hunch + hit go" path we avoid
  // the extra request.
  const steeringOptions = useSteeringOptions(advancedOpen);

  const steeringActive = hasAnySteering(steering);
  const steeringSurcharge = steeringActive ? 1 : 0;

  const remaining = me.data?.research_credits ?? 0;
  const totalCost = creditsBudget + (rush ? 1 : 0) + steeringSurcharge;
  const slotHours = creditsBudget * 96;

  // Re-clamp the slider when remaining drops (e.g. another tab spent
  // credits) or the rush / steering toggles flip. Keeps the UI
  // consistent with the wallet view returned by /api/auth/me.
  useEffect(() => {
    const surcharge = (rush ? 1 : 0) + steeringSurcharge;
    const cap = Math.max(1, remaining - surcharge);
    if (creditsBudget > cap) setCreditsBudget(cap);
    if (rush && remaining < 2 + steeringSurcharge) setRush(false);
  }, [remaining, rush, creditsBudget, steeringSurcharge]);

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    try {
      const steeringPayload = buildSteeringPayload(steering);
      const body: Parameters<typeof create.mutateAsync>[0] = {
        hunch: hunch.trim(),
        domain_hint: domainHint.trim() || null,
        credits_budget: creditsBudget,
        rush,
      };
      if (steeringPayload) body.steering = steeringPayload;
      const res = await create.mutateAsync(body);
      navigate({ to: '/research/$id', params: { id: res.job_id } });
    } catch (e) {
      if (isApiError(e)) {
        if (e.status === 402 && e.body && typeof e.body === 'object' && 'remaining' in e.body) {
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
    create.isPending || hunch.trim().length === 0 || totalCost > remaining || remaining === 0;

  const sliderMax = Math.max(1, remaining - (rush ? 1 : 0) - steeringSurcharge);
  const rushDisabled = !rush && remaining - creditsBudget - steeringSurcharge < 1;

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
              fontSize: 13,
              color: 'var(--ink-600)',
              display: 'flex',
              flexDirection: 'column',
              gap: 4,
            }}
          >
            <div
              style={{
                display: 'flex',
                justifyContent: 'space-between',
              }}
            >
              <span>
                Base: <strong>{creditsBudget}</strong> credit{creditsBudget === 1 ? '' : 's'}
              </span>
              <span>{remaining} remaining</span>
            </div>
            {rush && <div>+1 credit (rush surcharge)</div>}
            {steeringActive && <div>+1 credit (custom-steering surcharge)</div>}
            <div
              style={{
                marginTop: 2,
                paddingTop: 6,
                borderTop: '1px dashed var(--paper-300)',
                display: 'flex',
                justifyContent: 'space-between',
              }}
            >
              <span>
                Total: <strong>{totalCost}</strong> credit{totalCost === 1 ? '' : 's'}
              </span>
            </div>
          </div>
        </div>
      )}

      {remaining > 0 && (
        <AdvancedSteering
          open={advancedOpen}
          onToggle={setAdvancedOpen}
          state={steering}
          onChange={setSteering}
          options={steeringOptions.data ?? null}
          optionsLoading={steeringOptions.isPending && advancedOpen}
          optionsError={steeringOptions.error ? String(steeringOptions.error) : null}
        />
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

interface AdvancedSteeringProps {
  open: boolean;
  onToggle: (next: boolean) => void;
  state: SteeringFormState;
  onChange: (next: SteeringFormState) => void;
  options: SteeringOptions | null;
  optionsLoading: boolean;
  optionsError: string | null;
}

/**
 * Disclosure block under the basic submit form letting paying
 * researchers bias the GA's per-domain atom pool, mutation-operator
 * priors, and global mutation knobs. The shape the backend validator
 * expects lives in `lib/steering.ts::buildSteeringPayload`; this
 * component is pure UI state + a `prop`-driven setter.
 *
 * Atom names + operator names come from the server (so adding a new
 * atom is a backend-only change); render is a no-op until the options
 * query resolves.
 */
function AdvancedSteering({
  open,
  onToggle,
  state,
  onChange,
  options,
  optionsLoading,
  optionsError,
}: AdvancedSteeringProps) {
  return (
    <div style={{ marginTop: 20 }}>
      <button
        type="button"
        onClick={() => onToggle(!open)}
        aria-expanded={open}
        style={{
          background: 'transparent',
          border: '1px solid var(--paper-200)',
          borderRadius: 'var(--radius-md)',
          padding: '10px 12px',
          width: '100%',
          textAlign: 'left',
          cursor: 'pointer',
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'baseline',
          color: 'var(--ink-900)',
          fontSize: 14,
        }}
      >
        <span>
          <strong>Custom steering (advanced)</strong>
          <span className="hint" style={{ marginLeft: 8, fontWeight: 'normal', fontSize: 12 }}>
            +1 credit when any knob is set · overrides the LLM cluster steerer for this job
          </span>
        </span>
        <span aria-hidden style={{ fontFamily: 'var(--font-mono)' }}>
          {open ? '−' : '+'}
        </span>
      </button>

      {open && (
        <div
          style={{
            marginTop: 12,
            padding: 16,
            background: 'var(--bg-raised)',
            border: '1px solid var(--paper-200)',
            borderRadius: 'var(--radius-md)',
            display: 'flex',
            flexDirection: 'column',
            gap: 24,
          }}
        >
          {optionsLoading && <span className="hint">Loading steering options…</span>}
          {optionsError && (
            <span className="hint" role="alert" style={{ color: 'var(--danger-500)' }}>
              Couldn't load steering options: {optionsError}
            </span>
          )}
          {options && (
            <>
              <AtomPoolSection state={state} onChange={onChange} options={options} />
              <MutationPriorsSection state={state} onChange={onChange} options={options} />
              <MutationKnobsSection state={state} onChange={onChange} options={options} />
              <div>
                <button
                  type="button"
                  className="btn btn-secondary"
                  onClick={() => onChange(emptySteeringForm())}
                  style={{ fontSize: 12 }}
                >
                  Reset all steering
                </button>
              </div>
            </>
          )}
        </div>
      )}
    </div>
  );
}

interface SectionProps {
  state: SteeringFormState;
  onChange: (next: SteeringFormState) => void;
  options: SteeringOptions;
}

function AtomPoolSection({ state, onChange, options }: SectionProps) {
  const { domains, atom_names, bounds } = options;
  const w = bounds.atom_weight;
  return (
    <section>
      <h3 style={{ fontSize: 14, margin: '0 0 4px' }}>Atom pool weights</h3>
      <p className="hint" style={{ marginBottom: 12 }}>
        Per-domain bias toward physics-shape compounds. Weight {w.min.toFixed(1)}–{w.max.toFixed(1)}
        ; uncheck to drop the atom from the pool entirely.
      </p>
      <div style={{ display: 'flex', flexDirection: 'column', gap: 16 }}>
        {domains.map((domain) => {
          const picked = state.atomPool[domain] ?? {};
          return (
            <div key={domain}>
              <div style={{ fontSize: 13, marginBottom: 6, color: 'var(--ink-700)' }}>
                {prettyDomainKey(domain)}
              </div>
              <div
                style={{
                  display: 'grid',
                  gridTemplateColumns: 'repeat(auto-fill, minmax(220px, 1fr))',
                  gap: 8,
                }}
              >
                {atom_names.map((atom) => {
                  const isOn = atom in picked;
                  const value = picked[atom] ?? 1.0;
                  return (
                    <label
                      key={atom}
                      style={{
                        display: 'flex',
                        flexDirection: 'column',
                        gap: 4,
                        padding: 8,
                        background: isOn ? 'var(--paper-100, var(--bg-raised))' : 'transparent',
                        border: '1px solid var(--paper-200)',
                        borderRadius: 'var(--radius-sm)',
                        fontSize: 12,
                      }}
                    >
                      <span style={{ display: 'flex', justifyContent: 'space-between', gap: 6 }}>
                        <span style={{ display: 'flex', alignItems: 'center', gap: 6 }}>
                          <input
                            type="checkbox"
                            checked={isOn}
                            onChange={(e) => {
                              const nextDomain = { ...picked };
                              if (e.target.checked) {
                                nextDomain[atom] = value;
                              } else {
                                delete nextDomain[atom];
                              }
                              onChange({
                                ...state,
                                atomPool: { ...state.atomPool, [domain]: nextDomain },
                              });
                            }}
                          />
                          <code style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>
                            {atom}
                          </code>
                        </span>
                        <span style={{ fontFamily: 'var(--font-mono)', color: 'var(--ink-600)' }}>
                          {isOn ? value.toFixed(1) : '—'}
                        </span>
                      </span>
                      <input
                        type="range"
                        min={w.min}
                        max={w.max}
                        step={0.1}
                        value={value}
                        disabled={!isOn}
                        onChange={(e) => {
                          const v = Number(e.target.value);
                          onChange({
                            ...state,
                            atomPool: {
                              ...state.atomPool,
                              [domain]: { ...picked, [atom]: v },
                            },
                          });
                        }}
                      />
                    </label>
                  );
                })}
              </div>
            </div>
          );
        })}
      </div>
    </section>
  );
}

const COMMON_OPS = [
  'append_productive_suffix',
  'mutate_axiom_name',
  'mutate_param',
  'insert_random',
];

function MutationPriorsSection({ state, onChange, options }: SectionProps) {
  const allOps = options.operator_names;
  // Surface the four "common" operators the task calls out, but keep
  // them only if the backend still recognises them — falls back to the
  // server's list otherwise so a future MUTATION_OPS rename can't
  // strand the UI.
  const ops = useMemo(() => {
    const filtered = COMMON_OPS.filter((o) => allOps.includes(o));
    return filtered.length > 0 ? filtered : allOps.slice(0, 4);
  }, [allOps]);
  const w = options.bounds.mutation_prior;
  return (
    <section>
      <h3 style={{ fontSize: 14, margin: '0 0 4px' }}>Mutation priors</h3>
      <p className="hint" style={{ marginBottom: 12 }}>
        Per-operator bias for the GA's mutation picker. Slider {w.min.toFixed(1)}–{w.max.toFixed(1)}
        ; unset values fall back to the platform default (uniform 1.0).
      </p>
      <div style={{ display: 'flex', flexDirection: 'column', gap: 10 }}>
        {ops.map((op) => {
          const current = state.mutationPriors[op];
          const isOn = typeof current === 'number';
          const value = current ?? 1.0;
          return (
            <label
              key={op}
              style={{
                display: 'grid',
                gridTemplateColumns: '20px 1fr 60px 1fr',
                gap: 8,
                alignItems: 'center',
                fontSize: 13,
              }}
            >
              <input
                type="checkbox"
                checked={isOn}
                onChange={(e) => {
                  const next = { ...state.mutationPriors };
                  if (e.target.checked) {
                    next[op] = value;
                  } else {
                    delete next[op];
                  }
                  onChange({ ...state, mutationPriors: next });
                }}
              />
              <code style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>
                {prettyOperatorName(op)}
              </code>
              <span style={{ fontFamily: 'var(--font-mono)', color: 'var(--ink-600)' }}>
                {isOn ? value.toFixed(2) : '—'}
              </span>
              <input
                type="range"
                min={w.min}
                max={w.max}
                step={0.05}
                value={value}
                disabled={!isOn}
                onChange={(e) => {
                  onChange({
                    ...state,
                    mutationPriors: { ...state.mutationPriors, [op]: Number(e.target.value) },
                  });
                }}
              />
            </label>
          );
        })}
      </div>
    </section>
  );
}

type KnobKey = 'rate' | 'populationSize' | 'suffixBias' | 'elitismFraction';

function setKnob(
  state: SteeringFormState,
  key: KnobKey,
  next: number | undefined,
): SteeringFormState {
  const knobs = { ...state.mutationKnobs };
  if (next === undefined) {
    delete knobs[key];
  } else {
    knobs[key] = next;
  }
  return { ...state, mutationKnobs: knobs };
}

function MutationKnobsSection({ state, onChange, options }: SectionProps) {
  const b = options.bounds.mutation_knobs;
  return (
    <section>
      <h3 style={{ fontSize: 14, margin: '0 0 4px' }}>Mutation knobs</h3>
      <p className="hint" style={{ marginBottom: 12 }}>
        Global GA parameters. Each is optional — unchecked sliders fall back to the platform default
        for this job.
      </p>
      <div style={{ display: 'flex', flexDirection: 'column', gap: 10 }}>
        <KnobRow
          label="rate"
          help="Per-individual mutation probability per generation."
          min={b.rate.min}
          max={b.rate.max}
          step={0.01}
          value={state.mutationKnobs.rate}
          onChange={(v) => onChange(setKnob(state, 'rate', v))}
          format={(v) => v.toFixed(2)}
        />
        <KnobRow
          label="population_size"
          help="Individuals per generation. Larger = more exploration per chunk."
          min={b.population_size.min}
          max={b.population_size.max}
          step={b.population_size.step}
          value={state.mutationKnobs.populationSize}
          onChange={(v) => onChange(setKnob(state, 'populationSize', v))}
          format={(v) => v.toFixed(0)}
        />
        <KnobRow
          label="suffix_bias"
          help="Extra multiplier on append_productive_suffix on top of mutation_priors."
          min={b.suffix_bias.min}
          max={b.suffix_bias.max}
          step={0.05}
          value={state.mutationKnobs.suffixBias}
          onChange={(v) => onChange(setKnob(state, 'suffixBias', v))}
          format={(v) => v.toFixed(2)}
        />
        <KnobRow
          label="elitism_fraction"
          help="Fraction of each generation copied unchanged into the next."
          min={b.elitism_fraction.min}
          max={b.elitism_fraction.max}
          step={0.01}
          value={state.mutationKnobs.elitismFraction}
          onChange={(v) => onChange(setKnob(state, 'elitismFraction', v))}
          format={(v) => v.toFixed(2)}
        />
      </div>
    </section>
  );
}

interface KnobRowProps {
  label: string;
  help: string;
  min: number;
  max: number;
  step: number;
  value: number | undefined;
  onChange: (next: number | undefined) => void;
  format: (n: number) => string;
}

function KnobRow({ label, help, min, max, step, value, onChange, format }: KnobRowProps) {
  const isOn = typeof value === 'number';
  const display = isOn ? (value as number) : (min + max) / 2;
  return (
    <label
      style={{
        display: 'grid',
        gridTemplateColumns: '20px 1fr 80px 1fr',
        gap: 8,
        alignItems: 'center',
        fontSize: 13,
      }}
      title={help}
    >
      <input
        type="checkbox"
        checked={isOn}
        onChange={(e) => onChange(e.target.checked ? display : undefined)}
      />
      <code style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>{label}</code>
      <span style={{ fontFamily: 'var(--font-mono)', color: 'var(--ink-600)' }}>
        {isOn ? format(display) : '—'}
      </span>
      <input
        type="range"
        min={min}
        max={max}
        step={step}
        value={display}
        disabled={!isOn}
        onChange={(e) => onChange(Number(e.target.value))}
      />
    </label>
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
