import { createFileRoute, Link, redirect } from '@tanstack/react-router';
import { type CSSProperties, useState } from 'react';
import { CreateKeyDialog, RevealKeyModal } from '~/components/apikeys/CreateKeyDialog';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useApiKeys, useMe, useMyWorkers, useRevokeApiKey } from '~/lib/queries';
import type { NewApiKey, Worker } from '~/lib/types';

export const Route = createFileRoute('/api-keys')({ component: ApiKeysPage });

function ApiKeysPage() {
  const me = useMe();
  const { data, refetch } = useApiKeys();
  const { data: workersResp } = useMyWorkers();
  const revoke = useRevokeApiKey();
  const [createOpen, setCreateOpen] = useState(false);
  const [revealed, setRevealed] = useState<NewApiKey | null>(null);

  if (me.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });

  const keys = data?.keys ?? [];
  const workers = workersResp?.workers ?? [];
  const workerByName = new Map(workers.map((w) => [w.id, w]));

  return (
    <div className="app">
      <AppHeader active="api-keys" />
      <div className="container-wide" style={{ paddingTop: 32 }}>
        <div className="page-head">
          <span className="overline">For builders</span>
          <h1>
            API keys —{' '}
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              identify your scripts and your devices.
            </em>
          </h1>
          <p className="lede">
            <strong>Live</strong> keys (<code>nsk_live_…</code>) call the read API as you.{' '}
            <strong>Worker</strong> keys (<code>nsk_worker_…</code>) identify a specific device
            running the discovery binary — when that device verifies a theorem, the contribution is
            attributed to your account and the device label you set here.
          </p>
        </div>

        <div style={{ display: 'flex', justifyContent: 'flex-end', margin: '24px 0 16px' }}>
          <button type="button" className="btn btn-primary" onClick={() => setCreateOpen(true)}>
            + New key
          </button>
        </div>

        {keys.length === 0 ? (
          <div
            style={{
              padding: '64px 32px',
              textAlign: 'center',
              color: 'var(--ink-500)',
              fontSize: 15,
              border: '1px dashed var(--paper-300)',
              borderRadius: 'var(--radius-lg)',
              background: 'var(--paper-50)',
            }}
          >
            You don't have any API keys yet.{' '}
            <button
              type="button"
              className="btn btn-ghost"
              onClick={() => setCreateOpen(true)}
              style={{ display: 'inline', padding: 0 }}
            >
              Create the first one →
            </button>
          </div>
        ) : (
          <div className="card" style={{ padding: 0, overflow: 'hidden' }}>
            <table className="lead-table">
              <thead>
                <tr>
                  <th>Label</th>
                  <th>Kind</th>
                  <th>Prefix</th>
                  <th style={{ textAlign: 'right' }}>Worker status</th>
                  <th style={{ textAlign: 'right' }}>Theorems</th>
                  <th style={{ textAlign: 'right' }}>Last used</th>
                  <th style={{ textAlign: 'right' }} />
                </tr>
              </thead>
              <tbody>
                {keys.map((k) => {
                  const linkedWorker = k.kind === 'worker' ? workerByName.get(k.name) : undefined;
                  return (
                    <tr key={k.id}>
                      <td className="handle-cell">{k.name}</td>
                      <td>
                        <span
                          style={{
                            fontSize: 11,
                            letterSpacing: 'var(--tracking-allcaps)',
                            textTransform: 'uppercase',
                            fontWeight: 600,
                            color:
                              k.kind === 'worker' ? 'var(--terracotta-700)' : 'var(--olive-700)',
                          }}
                        >
                          {k.kind}
                        </span>
                      </td>
                      <td style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>{k.prefix}…</td>
                      <WorkerStatusCell worker={linkedWorker} kind={k.kind} />
                      <td className="num-cell">
                        {linkedWorker ? linkedWorker.theorems_contributed.toLocaleString() : '—'}
                      </td>
                      <td className="num-cell" style={{ color: 'var(--ink-500)' }}>
                        {k.last_used_at ? new Date(k.last_used_at).toLocaleString() : 'never'}
                      </td>
                      <td className="num-cell">
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
                  );
                })}
              </tbody>
            </table>
          </div>
        )}

        {workers.length > 0 && (
          <section style={{ marginTop: 56 }}>
            <h3 className="section-h" style={{ fontSize: 24, marginBottom: 8 }}>
              Your devices on the network
            </h3>
            <p style={{ color: 'var(--ink-500)', fontSize: 14, marginBottom: 24 }}>
              Live snapshot of every worker your account is running. Each row corresponds to a
              worker-kind API key and is publicly visible on{' '}
              <Link to="/workers">the workers page →</Link>
            </p>
            <div className="card" style={{ padding: 0, overflow: 'hidden' }}>
              <table className="lead-table">
                <thead>
                  <tr>
                    <th>Device</th>
                    <th>Host</th>
                    <th style={{ textAlign: 'right' }}>Status</th>
                    <th style={{ textAlign: 'right' }}>Generation</th>
                    <th style={{ textAlign: 'right' }}>Theorems</th>
                    <th style={{ textAlign: 'right' }}>Last verified</th>
                  </tr>
                </thead>
                <tbody>
                  {workers.map((w) => (
                    <MyWorkerRow key={w.id} w={w} />
                  ))}
                </tbody>
              </table>
            </div>
          </section>
        )}

        <UsageGuide />

        <p style={{ color: 'var(--ink-500)', fontSize: 13, margin: '40px 0' }}>
          Want to delete a worker entirely? Revoke its key here, then the worker disappears from
          your account. Past contributions stay attributed.
        </p>
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

function WorkerStatusCell({ worker, kind }: { worker: Worker | undefined; kind: string }) {
  if (kind !== 'worker') {
    return (
      <td className="num-cell" style={{ color: 'var(--ink-400)', fontStyle: 'italic' }}>
        n/a
      </td>
    );
  }
  if (!worker) {
    return (
      <td className="num-cell" style={{ color: 'var(--ink-400)' }}>
        not yet seen
      </td>
    );
  }
  const status = String(worker.status).toLowerCase();
  const color =
    status === 'active'
      ? 'var(--olive-700)'
      : status === 'inactive'
        ? 'var(--saffron-700)'
        : 'var(--ink-500)';
  return (
    <td
      className="num-cell"
      style={{
        color,
        textTransform: 'uppercase',
        letterSpacing: 'var(--tracking-allcaps)',
        fontSize: 11,
        fontWeight: 600,
      }}
    >
      {status}
    </td>
  );
}

function UsageGuide() {
  const codeStyle: CSSProperties = {
    fontFamily: 'var(--font-mono)',
    fontSize: 12,
    lineHeight: 1.55,
    background: 'var(--paper-50)',
    border: '1px solid var(--paper-300)',
    borderRadius: 'var(--radius-md)',
    padding: '12px 14px',
    overflow: 'auto',
    color: 'var(--ink-800)',
    whiteSpace: 'pre',
    margin: 0,
  };
  const cardStyle: CSSProperties = {
    padding: 24,
    display: 'flex',
    flexDirection: 'column',
    gap: 14,
  };
  return (
    <section style={{ marginTop: 56 }}>
      <h3 className="section-h" style={{ fontSize: 24, marginBottom: 8 }}>
        How to use a key
      </h3>
      <p style={{ color: 'var(--ink-500)', fontSize: 14, marginBottom: 24 }}>
        Each key is shown once when you create it. Save it in your password manager —{' '}
        <strong>we never store the cleartext</strong>.
      </p>
      <div
        style={{
          display: 'grid',
          gridTemplateColumns: 'repeat(auto-fit, minmax(320px, 1fr))',
          gap: 20,
        }}
      >
        <div className="card" style={cardStyle}>
          <header>
            <span className="overline" style={{ color: 'var(--olive-700)' }}>
              live key
            </span>
            <h4 style={{ margin: '4px 0 0', fontSize: 18 }}>
              Read the API as you{' '}
              <code style={{ color: 'var(--olive-700)', fontWeight: 400 }}>nsk_live_…</code>
            </h4>
          </header>
          <p style={{ fontSize: 14, color: 'var(--ink-700)', margin: 0 }}>
            For scripts, notebooks, and CLI tools. Counts against your plan's API-per-day quota and
            sees your private library / draft conjectures.
          </p>
          <pre style={codeStyle}>
            {`curl https://api.nasrudin.org/api/auth/me \\
  -H "Authorization: Bearer nsk_live_…"`}
          </pre>
          <p style={{ fontSize: 13, color: 'var(--ink-500)', margin: 0 }}>
            Pass the same <code>Authorization: Bearer …</code> header on every request. Browse the
            full surface at <Link to="/api-docs">/api-docs</Link>.
          </p>
        </div>

        <div className="card" style={cardStyle}>
          <header>
            <span className="overline" style={{ color: 'var(--terracotta-700)' }}>
              worker key
            </span>
            <h4 style={{ margin: '4px 0 0', fontSize: 18 }}>
              Donate compute{' '}
              <code style={{ color: 'var(--terracotta-700)', fontWeight: 400 }}>nsk_worker_…</code>
            </h4>
          </header>
          <p style={{ fontSize: 14, color: 'var(--ink-700)', margin: 0 }}>
            For the discovery binary running on a machine you control. Verified theorems are
            attributed to your account and the device label.
          </p>
          <ol style={{ fontSize: 13, color: 'var(--ink-700)', margin: 0, paddingLeft: 20 }}>
            <li style={{ marginBottom: 6 }}>
              Grab the bundle for your OS from{' '}
              <a
                href="https://github.com/Nasdin/nasrudin/releases/latest"
                target="_blank"
                rel="noreferrer"
              >
                the latest worker release ↗
              </a>{' '}
              (Linux x86_64, macOS x86_64 / arm64, Windows x86_64).
            </li>
            <li style={{ marginBottom: 6 }}>
              Install the Lean toolchain once:{' '}
              <code>
                curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
              </code>
            </li>
            <li>Extract and run with the key in the env:</li>
          </ol>
          <pre style={codeStyle}>
            {`tar xzf nasrudin-worker-*.tar.gz
cd nasrudin-worker-*

NASRUDIN_API_URL=https://api.nasrudin.org \\
NASRUDIN_WORKER_KEY=nsk_worker_… \\
NASRUDIN_WORKER_ID=my-laptop \\
./run.sh                # PowerShell: .\\run.ps1`}
          </pre>
          <p style={{ fontSize: 13, color: 'var(--ink-500)', margin: 0 }}>
            First run warms the Mathlib cache (~5 min). After that, the worker heartbeats every
            minute and verified theorems land on{' '}
            <Link to="/leaderboard">your leaderboard row →</Link>
          </p>
        </div>
      </div>
    </section>
  );
}

function MyWorkerRow({ w }: { w: Worker }) {
  const status = String(w.status).toLowerCase();
  return (
    <tr>
      <td className="handle-cell">
        <div style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
          <span
            style={{
              width: 7,
              height: 7,
              borderRadius: '50%',
              background:
                status === 'active'
                  ? 'var(--olive-500)'
                  : status === 'inactive'
                    ? 'var(--saffron-500)'
                    : 'var(--paper-300)',
              boxShadow: status === 'active' ? '0 0 0 3px var(--olive-50)' : 'none',
            }}
          />
          {w.id}
        </div>
      </td>
      <td
        style={{
          color: 'var(--ink-500)',
          fontFamily: 'var(--font-mono)',
          fontSize: 12,
        }}
      >
        {w.host ?? '—'}
      </td>
      <td
        className="num-cell"
        style={{
          color:
            status === 'active'
              ? 'var(--olive-700)'
              : status === 'inactive'
                ? 'var(--saffron-700)'
                : 'var(--ink-500)',
          textTransform: 'uppercase',
          letterSpacing: 'var(--tracking-allcaps)',
          fontSize: 11,
          fontWeight: 600,
        }}
      >
        {status}
      </td>
      <td className="num-cell">gen {(w.current_generation ?? 0).toLocaleString()}</td>
      <td className="num-cell">{w.theorems_contributed.toLocaleString()}</td>
      <td className="num-cell" style={{ color: 'var(--ink-500)' }}>
        {w.last_contribution_at ? new Date(w.last_contribution_at).toLocaleString() : '—'}
      </td>
    </tr>
  );
}
