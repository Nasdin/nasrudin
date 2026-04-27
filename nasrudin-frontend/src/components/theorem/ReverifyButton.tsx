import { useState } from 'react';

const STEPS = [
  'Fetching .lean file ...',
  'Resolving Mathlib imports ...',
  'Running lake build ...',
  'Verifying with Lean 4.10.0 ...',
  'QED — proof checks. ✓',
];

export function ReverifyButton() {
  const [state, setState] = useState<'idle' | 'running' | 'done'>('idle');
  const [step, setStep] = useState(0);

  function run() {
    setState('running');
    setStep(0);
    let s = 0;
    const t = setInterval(() => {
      s += 1;
      setStep(s);
      if (s >= STEPS.length) {
        clearInterval(t);
        setState('done');
      }
    }, 700);
  }

  return (
    <div>
      <button
        type="button"
        className="btn btn-primary"
        onClick={run}
        disabled={state === 'running'}
      >
        {state === 'idle' && 'Re-verify in browser →'}
        {state === 'running' && 'Verifying ...'}
        {state === 'done' && '✓ Verified locally'}
      </button>
      {state !== 'idle' && (
        <div
          style={{
            marginTop: 16,
            padding: 16,
            background: 'var(--ink-900)',
            color: 'var(--paper-100)',
            borderRadius: 10,
            fontFamily: 'var(--font-mono)',
            fontSize: 12.5,
            lineHeight: 1.7,
          }}
        >
          {STEPS.slice(0, step).map((s, i) => (
            <div
              key={s}
              style={{
                color:
                  i === step - 1 && state === 'running'
                    ? 'var(--saffron-300)'
                    : i === STEPS.length - 1
                      ? 'var(--olive-300)'
                      : 'var(--paper-300)',
              }}
            >
              {i === STEPS.length - 1 ? s : `[lake] ${s}`}
            </div>
          ))}
        </div>
      )}
    </div>
  );
}
