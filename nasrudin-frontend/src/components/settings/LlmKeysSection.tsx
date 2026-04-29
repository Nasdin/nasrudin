import { useState } from 'react';
import { isApiError } from '~/lib/api';
import { useLlmKeys, useRevokeLlmKey, useSetLlmKey } from '~/lib/queries';

export function LlmKeysSection() {
  const { data, isLoading, error } = useLlmKeys();
  const revoke = useRevokeLlmKey();
  const set = useSetLlmKey();
  const [showAdd, setShowAdd] = useState(false);
  const [provider, setProvider] = useState<string>('anthropic');
  const [keyInput, setKeyInput] = useState('');
  const [submitErr, setSubmitErr] = useState<string | null>(null);

  if (isLoading) {
    return (
      <div className="card" style={{ marginTop: 24 }}>
        Loading LLM keys…
      </div>
    );
  }

  // 503 → encrypt key not configured on server. Render a clear hint.
  if (error && isApiError(error) && error.status === 503) {
    return (
      <div className="card" style={{ marginTop: 24 }}>
        <h3 className="section-h" style={{ fontSize: 22, marginBottom: 16 }}>
          LLM providers
        </h3>
        <p style={{ color: 'var(--ink-500)' }}>
          LLM key vault is disabled. The server administrator must set
          <code> NASRUDIN_KEY_ENCRYPT</code> (32 random bytes, base64) before
          users can save provider keys.
        </p>
      </div>
    );
  }

  if (!data) return null;

  const knownProviders: string[] = data.known_providers ?? [];
  const keysByProvider = new Map(data.keys.map((k) => [k.provider, k]));

  async function onSave() {
    setSubmitErr(null);
    if (keyInput.trim().length === 0) {
      setSubmitErr('API key is empty');
      return;
    }
    try {
      await set.mutateAsync({ provider, key: keyInput });
      setKeyInput('');
      setShowAdd(false);
    } catch (e) {
      if (isApiError(e)) {
        const msg =
          e.body && typeof e.body === 'object' && 'error' in e.body
            ? String((e.body as { error: unknown }).error)
            : `Request failed (${e.status})`;
        setSubmitErr(msg);
      } else {
        setSubmitErr('Network error');
      }
    }
  }

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
          LLM providers
        </h3>
        {!showAdd && (
          <button className="btn btn-primary" onClick={() => setShowAdd(true)}>
            Add key
          </button>
        )}
      </div>

      <ul style={{ listStyle: 'none', margin: 0, padding: 0 }}>
        {knownProviders.map((p) => {
          const row = keysByProvider.get(p);
          return (
            <li
              key={p}
              style={{
                display: 'flex',
                alignItems: 'center',
                gap: 16,
                padding: '12px 0',
                borderTop: '1px solid var(--paper-200)',
              }}
            >
              <span
                style={{ fontFamily: 'var(--font-mono)', minWidth: 100, fontWeight: 500 }}
              >
                {p}
              </span>
              {row ? (
                <>
                  <span
                    style={{ fontFamily: 'var(--font-mono)', color: 'var(--ink-700)' }}
                  >
                    ····{row.key_hint}
                  </span>
                  <span
                    style={{ color: 'var(--ink-500)', fontSize: 13, flex: 1 }}
                  >
                    {row.last_used_at
                      ? `last used ${new Date(row.last_used_at).toLocaleString()}`
                      : 'never used'}
                  </span>
                  <button
                    className="btn btn-link"
                    style={{ color: 'var(--danger-500)' }}
                    onClick={() => revoke.mutate(p)}
                    disabled={revoke.isPending}
                  >
                    Revoke
                  </button>
                </>
              ) : (
                <span
                  style={{ color: 'var(--ink-500)', fontStyle: 'italic', flex: 1 }}
                >
                  No key configured
                </span>
              )}
            </li>
          );
        })}
      </ul>

      {showAdd && (
        <div
          style={{
            marginTop: 16,
            padding: 16,
            border: '1px solid var(--paper-200)',
            borderRadius: 8,
          }}
        >
          <div className="field">
            <label htmlFor="llm-provider">Provider</label>
            <select
              id="llm-provider"
              value={provider}
              onChange={(e) => setProvider(e.target.value)}
            >
              {knownProviders.map((p) => (
                <option key={p} value={p}>
                  {p}
                </option>
              ))}
            </select>
          </div>
          <div className="field">
            <label htmlFor="llm-key">API key</label>
            <input
              id="llm-key"
              type="password"
              value={keyInput}
              onChange={(e) => setKeyInput(e.target.value)}
              placeholder="sk-…"
              autoFocus
            />
            <span className="hint">
              The plaintext is sent over HTTPS; the server encrypts with AES-256-GCM
              before persisting. Only the last 4 chars are stored separately for UI
              display.
            </span>
          </div>
          {submitErr && (
            <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13 }}>
              {submitErr}
            </div>
          )}
          <div style={{ display: 'flex', gap: 12, marginTop: 12 }}>
            <button
              className="btn btn-primary"
              onClick={onSave}
              disabled={set.isPending || keyInput.trim().length === 0}
            >
              {set.isPending ? 'Saving…' : 'Save key'}
            </button>
            <button
              className="btn btn-secondary"
              onClick={() => {
                setShowAdd(false);
                setKeyInput('');
                setSubmitErr(null);
              }}
            >
              Cancel
            </button>
          </div>
        </div>
      )}
    </div>
  );
}
