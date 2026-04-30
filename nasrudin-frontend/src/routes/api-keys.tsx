import { createFileRoute, Link, redirect } from '@tanstack/react-router';
import {
  flexRender,
  getCoreRowModel,
  useReactTable,
  type ColumnDef,
  type SortingState,
} from '@tanstack/react-table';
import { type CSSProperties, useState } from 'react';
import { CreateKeyDialog, RevealKeyModal } from '~/components/apikeys/CreateKeyDialog';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useApiKeys, useMe, useMyWorkers, useRevokeApiKey } from '~/lib/queries';
import type { ApiKeySummary, NewApiKey, Worker } from '~/lib/types';

export const Route = createFileRoute('/api-keys')({ component: ApiKeysPage });

function ApiKeysPage() {
  const me = useMe();
  const { data, refetch } = useApiKeys();
  const { data: workersResp } = useMyWorkers();
  const revoke = useRevokeApiKey();
  const [createOpen, setCreateOpen] = useState(false);
  const [revealed, setRevealed] = useState<NewApiKey | null>(null);
  const [sorting, setSorting] = useState<SortingState>([]);

  if (me.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });

  const keys = data?.keys ?? [];
  const workers = workersResp?.workers ?? [];
  const workerByName = new Map(workers.map((w) => [w.id, w]));

  const columns: ColumnDef<ApiKeySummary>[] = [
    {
      accessorKey: 'name',
      header: 'Label',
      cell: (info) => <span className="handle-cell">{info.getValue() as string}</span>,
    },
    {
      accessorKey: 'kind',
      header: 'Kind',
      cell: (info) => {
        const kind = info.getValue() as string;
        return (
          <span
            style={{
              fontSize: 11,
              letterSpacing: 'var(--tracking-allcaps)',
              textTransform: 'uppercase',
              fontWeight: 600,
              color: kind === 'worker' ? 'var(--terracotta-700)' : 'var(--olive-700)',
            }}
          >
            {kind}
          </span>
        );
      },
    },
    {
      accessorKey: 'prefix',
      header: 'Prefix',
      cell: (info) => (
        <span style={{ fontFamily: 'var(--font-mono)', fontSize: 12 }}>
          {info.getValue() as string}…
        </span>
      ),
    },
    {
      id: 'workerStatus',
      header: 'Worker status',
      cell: (info) => {
        const row = info.row.original;
        const linkedWorker = row.kind === 'worker' ? workerByName.get(row.name) : undefined;
        const status = linkedWorker ? String(linkedWorker.status).toLowerCase() : null;
        const color =
          status === 'active'
            ? 'var(--olive-700)'
            : status === 'inactive'
              ? 'var(--saffron-700)'
              : 'var(--ink-500)';
        if (row.kind !== 'worker') {
          return (
            <span style={{ color: 'var(--ink-400)', fontStyle: 'italic' }}>n/a</span>
          );
        }
        if (!linkedWorker) {
          return <span style={{ color: 'var(--ink-400)' }}>not yet seen</span>;
        }
        return (
          <span
            style={{
              color,
              textTransform: 'uppercase',
              letterSpacing: 'var(--tracking-allcaps)',
              fontSize: 11,
              fontWeight: 600,
            }}
          >
            {status}
          </span>
        );
      },
    },
    {
      id: 'theorems',
      header: 'Theorems',
      cell: (info) => {
        const row = info.row.original;
        const linkedWorker = row.kind === 'worker' ? workerByName.get(row.name) : undefined;
        return (
          <span className="num-cell">
            {linkedWorker ? linkedWorker.theorems_contributed.toLocaleString() : '—'}
          </span>
        );
      },
    },
    {
      accessorKey: 'last_used_at',
      header: 'Last used',
      cell: (info) => {
        const lastUsed = info.getValue() as string | null;
        return (
          <span className="num-cell" style={{ color: 'var(--ink-500)' }}>
            {lastUsed ? new Date(lastUsed).toLocaleString() : 'never'}
          </span>
        );
      },
    },
    {
      id: 'actions',
      header: '',
      cell: (info) => {
        const row = info.row.original;
        return (
          <button
            type="button"
            className="btn btn-ghost"
            onClick={async () => {
              if (confirm(`Revoke key "${row.name}"?`)) {
                await revoke.mutateAsync(row.id);
                refetch();
              }
            }}
          >
            Revoke
          </button>
        );
      },
    },
  ];

  const table = useReactTable({
    data: keys,
    columns,
    getCoreRowModel: getCoreRowModel(),
    onSortingChange: setSorting,
    state: { sorting },
  });

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
                {table.getHeaderGroups().map((headerGroup) => (
                  <tr key={headerGroup.id}>
                    {headerGroup.headers.map((header) => (
                      <th
                        key={header.id}
                        style={{
                          textAlign: header.column.id === 'actions' ? 'right' : 'left',
                          cursor: header.column.getCanSort() ? 'pointer' : 'default',
                        }}
                        onClick={header.column.getToggleSortingHandler()}
                      >
                        {header.isPlaceholder
                          ? null
                          : header.column.columnDef.header}
                        {header.column.getIsSorted() === 'asc' ? ' ↑' : null}
                        {header.column.getIsSorted() === 'desc' ? ' ↓' : null}
                      </th>
                    ))}
                  </tr>
                ))}
              </thead>
              <tbody>
                {table.getRowModel().rows.map((row) => (
                  <tr key={row.id}>
                    {row.getVisibleCells().map((cell) => {
                      const isActions = cell.column.id === 'actions';
                      const isTheorems = cell.column.id === 'theorems';
                      const isWorkerStatus = cell.column.id === 'workerStatus';
                      const isLastUsed = cell.column.id === 'last_used_at';
                      return (
                        <td
                          key={cell.id}
                          className={isActions || isTheorems || isWorkerStatus || isLastUsed ? 'num-cell' : ''}
                          style={{
                            textAlign: isActions ? 'right' : 'left',
                          }}
                        >
                          {flexRender(cell.column.columnDef.cell, cell.getContext())}
                        </td>
                      );
                    })}
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        )}

        {workers.length > 0 && <WorkersTable workers={workers} />}

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

function WorkersTable({ workers }: { workers: Worker[] }) {
  const [sorting, setSorting] = useState<SortingState>([]);

  const columns: ColumnDef<Worker>[] = [
    {
      accessorKey: 'id',
      header: 'Device',
      cell: (info) => {
        const w = info.row.original;
        const status = String(w.status).toLowerCase();
        return (
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
            <span className="handle-cell">{w.id}</span>
          </div>
        );
      },
    },
    {
      accessorKey: 'host',
      header: 'Host',
      cell: (info) => {
        const host = info.getValue() as string | null;
        return (
          <span style={{ color: 'var(--ink-500)', fontFamily: 'var(--font-mono)', fontSize: 12 }}>
            {host ?? '—'}
          </span>
        );
      },
    },
    {
      id: 'status',
      header: 'Status',
      cell: (info) => {
        const w = info.row.original;
        const status = String(w.status).toLowerCase();
        const color =
          status === 'active'
            ? 'var(--olive-700)'
            : status === 'inactive'
              ? 'var(--saffron-700)'
              : 'var(--ink-500)';
        return (
          <span
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
          </span>
        );
      },
    },
    {
      id: 'generation',
      header: 'Generation',
      cell: (info) => {
        const w = info.row.original;
        return (
          <span className="num-cell">gen {(w.current_generation ?? 0).toLocaleString()}</span>
        );
      },
    },
    {
      accessorKey: 'theorems_contributed',
      header: 'Theorems',
      cell: (info) => (
        <span className="num-cell">{(info.getValue() as number).toLocaleString()}</span>
      ),
    },
    {
      id: 'lastVerified',
      header: 'Last verified',
      cell: (info) => {
        const w = info.row.original;
        return (
          <span className="num-cell" style={{ color: 'var(--ink-500)' }}>
            {w.last_contribution_at ? new Date(w.last_contribution_at).toLocaleString() : '—'}
          </span>
        );
      },
    },
  ];

  const table = useReactTable({
    data: workers,
    columns,
    getCoreRowModel: getCoreRowModel(),
    onSortingChange: setSorting,
    state: { sorting },
  });

  return (
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
            {table.getHeaderGroups().map((headerGroup) => (
              <tr key={headerGroup.id}>
                {headerGroup.headers.map((header) => (
                  <th
                    key={header.id}
                    style={{
                      textAlign: 'right',
                      cursor: header.column.getCanSort() ? 'pointer' : 'default',
                    }}
                    onClick={header.column.getToggleSortingHandler()}
                  >
                    {header.isPlaceholder ? null : header.column.columnDef.header}
                    {header.column.getIsSorted() === 'asc' ? ' ↑' : null}
                    {header.column.getIsSorted() === 'desc' ? ' ↓' : null}
                  </th>
                ))}
              </tr>
            ))}
          </thead>
          <tbody>
            {table.getRowModel().rows.map((row) => (
              <tr key={row.id}>
                {row.getVisibleCells().map((cell) => (
                  <td
                    key={cell.id}
                    className="num-cell"
                    style={{ textAlign: 'right' }}
                  >
                    {flexRender(cell.column.columnDef.cell, cell.getContext())}
                  </td>
                ))}
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </section>
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

