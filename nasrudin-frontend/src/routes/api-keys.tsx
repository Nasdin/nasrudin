import { createFileRoute, redirect } from '@tanstack/react-router';
import { useState } from 'react';
import { CreateKeyDialog, RevealKeyModal } from '~/components/apikeys/CreateKeyDialog';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useApiKeys, useMe, useRevokeApiKey } from '~/lib/queries';
import type { NewApiKey } from '~/lib/types';

export const Route = createFileRoute('/api-keys')({ component: ApiKeysPage });

function ApiKeysPage() {
  const me = useMe();
  const { data, refetch } = useApiKeys();
  const revoke = useRevokeApiKey();
  const [createOpen, setCreateOpen] = useState(false);
  const [revealed, setRevealed] = useState<NewApiKey | null>(null);

  if (me.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });

  const keys = data?.keys ?? [];

  return (
    <div className="app">
      <AppHeader active="api-keys" />
      <div className="container-wide" style={{ paddingTop: 32 }}>
        <div className="page-head">
          <span className="overline">For builders</span>
          <h1>API keys</h1>
          <p className="lede">
            Use a key as a Bearer token to call the Nasrudin API from your scripts and apps.
          </p>
        </div>
        <div style={{ display: 'flex', justifyContent: 'flex-end', marginBottom: 16 }}>
          <button type="button" className="btn btn-primary" onClick={() => setCreateOpen(true)}>
            + New key
          </button>
        </div>
        {keys.length === 0 ? (
          <p style={{ color: 'var(--ink-500)' }}>You don't have any API keys yet.</p>
        ) : (
          <table className="lead-table">
            <thead>
              <tr>
                <th>Name</th>
                <th>Kind</th>
                <th>Prefix</th>
                <th>Created</th>
                <th>Last used</th>
                <th />
              </tr>
            </thead>
            <tbody>
              {keys.map((k) => (
                <tr key={k.id}>
                  <td>{k.name}</td>
                  <td>
                    <code style={{ fontSize: 12, color: 'var(--ink-500)' }}>
                      {k.kind ?? 'live'}
                    </code>
                  </td>
                  <td style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>{k.prefix}…</td>
                  <td>{new Date(k.created_at).toLocaleDateString()}</td>
                  <td>{k.last_used_at ? new Date(k.last_used_at).toLocaleString() : '—'}</td>
                  <td>
                    <button
                      type="button"
                      className="btn btn-ghost"
                      onClick={async () => {
                        if (confirm(`Revoke key "${k.name}"?`)) {
                          await revoke.mutateAsync(k.id);
                          refetch();
                        }
                      }}
                    >
                      Revoke
                    </button>
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        )}
      </div>
      <AppFooter />
      {createOpen && (
        <CreateKeyDialog
          onClose={() => setCreateOpen(false)}
          onCreated={(k) => {
            setCreateOpen(false);
            setRevealed(k);
          }}
        />
      )}
      {revealed && (
        <RevealKeyModal keyValue={revealed.full_key} onClose={() => setRevealed(null)} />
      )}
    </div>
  );
}
