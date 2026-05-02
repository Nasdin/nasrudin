import { createFileRoute, useNavigate } from '@tanstack/react-router';
import { type FormEvent, useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { SignInPrompt } from '~/components/platform/SignInPrompt';
import { isApiError } from '~/lib/api';
import { useCreateConjecture, useMe } from '~/lib/queries';

export const Route = createFileRoute('/conjecture')({ component: ConjecturePage });

function ConjecturePage() {
  const me = useMe();
  const navigate = useNavigate();
  const create = useCreateConjecture();

  const [hunch, setHunch] = useState('');
  const [domainHint, setDomainHint] = useState('');
  const [model, setModel] = useState('claude-sonnet-4-6');
  const [wallSeconds, setWallSeconds] = useState(600);
  const [maxCandidates, setMaxCandidates] = useState(100_000);
  const [error, setError] = useState<string | null>(null);

  if (me.isPending) return null;
  if (!me.data)
    return (
      <SignInPrompt
        active="conjecture"
        overline="Research"
        title="New conjecture"
        description="Describe a hypothesis in plain English and the router hands it to your chosen LLM, which proposes seed axioms + initial populations. Sign in to submit one."
      />
    );

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    try {
      const res = await create.mutateAsync({
        hunch: hunch.trim(),
        domain_hint: domainHint.trim() || null,
        provider: 'anthropic',
        model,
        budget: { wall_seconds: wallSeconds, max_candidates: maxCandidates },
      });
      navigate({ to: '/conjecture/$id', params: { id: res.job_id } });
    } catch (e) {
      if (isApiError(e)) {
        const msg =
          e.body && typeof e.body === 'object' && 'error' in e.body
            ? String((e.body as { error: unknown }).error)
            : `Request failed (${e.status})`;
        setError(msg);
      } else {
        setError('Network error');
      }
    }
  }

  return (
    <div className="app">
      <AppHeader active="conjecture" />
      <div className="container-wide" style={{ maxWidth: 760 }}>
        <div className="page-head">
          <span className="overline">Research</span>
          <h1>
            New conjecture —{' '}
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              what should we try to derive?
            </em>
          </h1>
          <p className="lede">
            Describe a hypothesis in plain English. The router hands it to your chosen LLM, which
            proposes seed axiom subsets + initial populations. Pick one and a research-mode worker
            picks the run up.
          </p>
        </div>

        <form className="page-body" onSubmit={onSubmit} style={{ maxWidth: 560 }}>
          <div className="field">
            <label htmlFor="hunch">Hunch</label>
            <textarea
              id="hunch"
              value={hunch}
              onChange={(e) => setHunch(e.target.value)}
              rows={5}
              required
              placeholder="Energy and rest mass should relate via the speed of light squared."
              style={{
                background: 'var(--bg-raised)',
                border: '1px solid var(--paper-200)',
                borderRadius: 'var(--radius-md)',
                padding: '12px 14px',
                fontFamily: 'var(--font-sans)',
                fontSize: 15,
                color: 'var(--ink-900)',
                resize: 'vertical',
              }}
            />
            <span className="hint">
              Plain English. The LLM never proves; it only points the GA.
            </span>
          </div>

          <div className="field">
            <label htmlFor="domain">Domain hint (optional)</label>
            <select
              id="domain"
              value={domainHint}
              onChange={(e) => setDomainHint(e.target.value)}
            >
              <option value="">—</option>
              <option value="SpecialRelativity">SpecialRelativity</option>
              <option value="ClassicalMechanics">ClassicalMechanics</option>
              <option value="Electromagnetism">Electromagnetism</option>
              <option value="QuantumMechanics">QuantumMechanics</option>
              <option value="QuantumFieldTheory">QuantumFieldTheory</option>
              <option value="Thermodynamics">Thermodynamics</option>
              <option value="StatisticalMechanics">StatisticalMechanics</option>
              <option value="GeneralRelativity">GeneralRelativity</option>
              <option value="FluidDynamics">FluidDynamics</option>
              <option value="Optics">Optics</option>
              <option value="PureMath">PureMath</option>
            </select>
          </div>

          <div className="field">
            <label htmlFor="model">Model</label>
            <select id="model" value={model} onChange={(e) => setModel(e.target.value)}>
              <option value="claude-sonnet-4-6">Claude Sonnet 4.6</option>
              <option value="claude-opus-4-7">Claude Opus 4.7</option>
              <option value="claude-haiku-4-5">Claude Haiku 4.5</option>
            </select>
            <span className="hint">
              Anthropic only for Phase D launch. Configure your API key in <a href="/settings">Settings</a>.
            </span>
          </div>

          <div style={{ display: 'flex', gap: 16 }}>
            <div className="field" style={{ flex: 1 }}>
              <label htmlFor="wall">Wall seconds</label>
              <input
                id="wall"
                type="number"
                min={60}
                max={86_400}
                value={wallSeconds}
                onChange={(e) => setWallSeconds(Number(e.target.value))}
              />
            </div>
            <div className="field" style={{ flex: 1 }}>
              <label htmlFor="cands">Max candidates</label>
              <input
                id="cands"
                type="number"
                min={1000}
                max={10_000_000}
                value={maxCandidates}
                onChange={(e) => setMaxCandidates(Number(e.target.value))}
              />
            </div>
          </div>

          {error && (
            <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginTop: 12 }}>
              {error}
            </div>
          )}
          <div style={{ marginTop: 24, display: 'flex', gap: 12 }}>
            <button
              type="submit"
              className="btn btn-primary"
              disabled={create.isPending || hunch.trim().length === 0}
            >
              {create.isPending ? 'Calling LLM…' : 'Get suggestions'}
            </button>
          </div>
        </form>
      </div>
      <AppFooter />
    </div>
  );
}
