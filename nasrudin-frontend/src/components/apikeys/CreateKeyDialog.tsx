import { useState } from 'react';
import { useCreateApiKey } from '~/lib/queries';
import type { ApiKeyKind, NewApiKey } from '~/lib/types';

export function CreateKeyDialog({
  onClose,
  onCreated,
}: {
  onClose: () => void;
  onCreated: (k: NewApiKey) => void;
}) {
  const [name, setName] = useState('');
  const [kind, setKind] = useState<ApiKeyKind>('live');
  const [error, setError] = useState<string | null>(null);
  const create = useCreateApiKey();

  async function submit() {
    setError(null);
    if (!name.trim()) {
      setError('name required');
      return;
    }
    try {
      const key = await create.mutateAsync({ name: name.trim(), kind });
      onCreated(key);
    } catch (e) {
      setError(e instanceof Error ? e.message : 'failed');
    }
  }

  return (
    <div
      role="dialog"
      aria-modal
      style={{
        position: 'fixed',
        inset: 0,
        background: 'rgba(42,33,26,0.55)',
        display: 'grid',
        placeItems: 'center',
        zIndex: 100,
      }}
    >
      <div
        style={{
          background: 'var(--bg-raised)',
          padding: 32,
          borderRadius: 12,
          width: 460,
          maxWidth: '90vw',
        }}
      >
        <h3 style={{ fontFamily: 'var(--font-serif)', fontSize: 24, marginBottom: 16 }}>
          Create an API key
        </h3>
        <div className="field">
          <label htmlFor="key-name">Name</label>
          <input
            id="key-name"
            // biome-ignore lint/a11y/noAutofocus: dialog opens on user click, focus is expected
            autoFocus
            value={name}
            onChange={(e) => setName(e.target.value)}
            placeholder={kind === 'worker' ? 'my-laptop-worker' : 'my-laptop'}
          />
          <span className="hint">
            {kind === 'worker'
              ? 'Identifies this worker in the leaderboard and heartbeat log.'
              : 'A short label so you remember what this key is for.'}
          </span>
        </div>
        <div className="field" style={{ marginTop: 16 }}>
          <span className="label">Kind</span>
          <div style={{ display: 'flex', gap: 12, marginTop: 8 }}>
            <label style={{ display: 'flex', gap: 6, alignItems: 'center', cursor: 'pointer' }}>
              <input
                type="radio"
                name="kind"
                value="live"
                checked={kind === 'live'}
                onChange={() => setKind('live')}
              />
              <span>
                <strong>Live</strong> — read API + scripts (<code>nsk_live_…</code>)
              </span>
            </label>
            <label style={{ display: 'flex', gap: 6, alignItems: 'center', cursor: 'pointer' }}>
              <input
                type="radio"
                name="kind"
                value="worker"
                checked={kind === 'worker'}
                onChange={() => setKind('worker')}
              />
              <span>
                <strong>Worker</strong> — discovery binary (<code>nsk_worker_…</code>)
              </span>
            </label>
          </div>
        </div>
        {error && (
          <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13 }}>
            {error}
          </div>
        )}
        <div style={{ display: 'flex', gap: 12, marginTop: 24, justifyContent: 'flex-end' }}>
          <button type="button" className="btn btn-secondary" onClick={onClose}>
            Cancel
          </button>
          <button
            type="button"
            className="btn btn-primary"
            onClick={submit}
            disabled={create.isPending}
          >
            {create.isPending ? 'Creating…' : 'Create key'}
          </button>
        </div>
      </div>
    </div>
  );
}

export function RevealKeyModal({ keyValue, onClose }: { keyValue: string; onClose: () => void }) {
  const [acknowledged, setAck] = useState(false);
  const isWorker = keyValue.startsWith('nsk_worker_');
  return (
    <div
      role="dialog"
      aria-modal
      style={{
        position: 'fixed',
        inset: 0,
        background: 'rgba(42,33,26,0.55)',
        display: 'grid',
        placeItems: 'center',
        zIndex: 101,
      }}
    >
      <div
        style={{
          background: 'var(--bg-raised)',
          padding: 32,
          borderRadius: 12,
          width: 560,
          maxWidth: '90vw',
        }}
      >
        <h3 style={{ fontFamily: 'var(--font-serif)', fontSize: 24, marginBottom: 8 }}>
          Save this key — it won't be shown again.
        </h3>
        <p style={{ color: 'var(--ink-700)', fontSize: 14, marginBottom: 16 }}>
          Once you close this window, the secret is gone. We only store a hashed copy.
        </p>
        <pre className="code-block" style={{ overflow: 'auto', userSelect: 'all' }}>
          {keyValue}
        </pre>
        <button
          type="button"
          className="btn btn-secondary"
          onClick={() => navigator.clipboard.writeText(keyValue)}
          style={{ marginTop: 12 }}
        >
          Copy to clipboard
        </button>
        {isWorker && (
          <div style={{ marginTop: 16, fontSize: 13 }}>
            <p style={{ color: 'var(--ink-700)', marginBottom: 8 }}>
              Run the discovery worker on your machine:
            </p>
            <pre
              className="code-block"
              style={{ fontSize: 12, padding: 12, overflow: 'auto', userSelect: 'all' }}
            >{`curl -L https://github.com/nasdin/nasrudin/releases/latest/download/nasrudin-worker-$(uname -s | tr A-Z a-z)-$(uname -m).tar.gz | tar xz
NASRUDIN_API_URL=https://api.nasrudin.org \\
NASRUDIN_WORKER_KEY=${keyValue} \\
./nasrudin-worker --gens 100 --pop 64`}</pre>
          </div>
        )}
        <label
          style={{ display: 'flex', gap: 8, alignItems: 'center', marginTop: 24, fontSize: 13 }}
        >
          <input
            type="checkbox"
            checked={acknowledged}
            onChange={(e) => setAck(e.target.checked)}
          />
          I have copied this key somewhere safe.
        </label>
        <div style={{ display: 'flex', justifyContent: 'flex-end', marginTop: 16 }}>
          <button
            type="button"
            className="btn btn-primary"
            disabled={!acknowledged}
            onClick={onClose}
          >
            Done
          </button>
        </div>
      </div>
    </div>
  );
}
