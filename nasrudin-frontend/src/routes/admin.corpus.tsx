import { createFileRoute } from '@tanstack/react-router';
import { useState } from 'react';
import { adminFetch } from '~/lib/adminApi';

export const Route = createFileRoute('/admin/corpus')({ component: CorpusPage });

function CorpusPage() {
  const [last, setLast] = useState<unknown>(null);
  const [busy, setBusy] = useState(false);

  const reload = async () => {
    const reason = window.prompt('Reason for corpus reload (≥ 10 chars):');
    if (!reason || reason.trim().length < 10) return;
    setBusy(true);
    try {
      const r = await adminFetch<unknown>('/api/admin/reload_corpus', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ reason: reason.trim() }),
      });
      setLast(r);
    } finally {
      setBusy(false);
    }
  };

  return (
    <section>
      <h1>Corpus</h1>
      <p>
        Hot-reloads the AxiomStore from disk after a fresh{' '}
        <code>lake exe extract</code> run. Workers see the new building
        blocks on their next /api/seed poll.
      </p>
      <button disabled={busy} onClick={() => void reload()}>
        {busy ? 'Reloading…' : 'Reload corpus'}
      </button>
      {last !== null && (
        <pre style={{ marginTop: 16, background: 'var(--paper-100)', padding: 12 }}>
          {JSON.stringify(last, null, 2)}
        </pre>
      )}
    </section>
  );
}
