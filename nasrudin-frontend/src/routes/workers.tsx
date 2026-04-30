import { createFileRoute, Link } from '@tanstack/react-router';
import {
  flexRender,
  getCoreRowModel,
  useReactTable,
  type ColumnDef,
  type SortingState,
} from '@tanstack/react-table';
import { useState } from 'react';
import { NetworkBreakdown } from '~/components/landing/NetworkBreakdown';
import { PulseStrip } from '~/components/landing/PulseStrip';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useWorkers } from '~/lib/queries';
import type { Worker } from '~/lib/types';

export const Route = createFileRoute('/workers')({ component: WorkersPage });

type StatusFilter = 'all' | 'active' | 'inactive' | 'disconnected';

function WorkersPage() {
  const { data, isPending } = useWorkers();
  const [filter, setFilter] = useState<StatusFilter>('all');
  const [sorting, setSorting] = useState<SortingState>([]);
  const all = data ?? [];
  const filtered =
    filter === 'all' ? all : all.filter((w) => String(w.status).toLowerCase() === filter);

  const active = all.filter((w) => String(w.status).toLowerCase() === 'active').length;
  const totalThm = all.reduce((s, w) => s + w.theorems_contributed, 0);

  return (
    <div className="app">
      <AppHeader active="workers" />
      <div className="container-wide">
        <div className="page-head">
          <span className="overline">The network</span>
          <h1>
            Workers —{' '}
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              who's running, what they last verified.
            </em>
          </h1>
          <p className="lede">
            Every worker on the platform, attributed to its owner. Each row shows the worker's
            current status, host, owner, and the moment its last verified theorem was accepted by
            the central server. Anonymous workers (registered without a user account) appear without
            an owner.
          </p>
        </div>

        <div style={{ marginTop: 24, marginBottom: 24 }}>
          <PulseStrip />
        </div>

        <div className="stat-row stat-row-3" style={{ marginTop: 24, marginBottom: 32 }}>
          <div className="stat-cell">
            <div className="label">Workers · live</div>
            <div className="num">{active}</div>
            <div className="delta">of {all.length} registered</div>
          </div>
          <div className="stat-cell">
            <div className="label">Theorems contributed</div>
            <div className="num">{totalThm.toLocaleString()}</div>
            <div className="delta">across all workers</div>
          </div>
          <div className="stat-cell">
            <div className="label">Run a worker</div>
            <div className="num" style={{ fontSize: 22 }}>
              <Link to="/api-keys">Get a worker key →</Link>
            </div>
            <div className="delta">attribution is automatic</div>
          </div>
        </div>

        <div style={{ marginBottom: 32 }}>
          <NetworkBreakdown />
        </div>

        <div className="lead-tabs" style={{ marginBottom: 16 }}>
          <FilterTab value="all" current={filter} setFilter={setFilter}>
            All · {all.length}
          </FilterTab>
          <FilterTab value="active" current={filter} setFilter={setFilter}>
            Active · {active}
          </FilterTab>
          <FilterTab value="inactive" current={filter} setFilter={setFilter}>
            Inactive · {all.filter((w) => String(w.status).toLowerCase() === 'inactive').length}
          </FilterTab>
          <FilterTab value="disconnected" current={filter} setFilter={setFilter}>
            Off · {all.filter((w) => String(w.status).toLowerCase() === 'disconnected').length}
          </FilterTab>
        </div>

        <div className="page-body" style={{ paddingTop: 0 }}>
          {isPending && <p style={{ color: 'var(--ink-500)' }}>loading…</p>}
          {!isPending && filtered.length === 0 && (
            <p style={{ color: 'var(--ink-500)', padding: 32 }}>
              No workers in this view. Try a different filter, or be the first to{' '}
              <Link to="/api-keys">spin one up →</Link>
            </p>
          )}
          {filtered.length > 0 && (
            <div className="lead-table-scroll">
              <WorkersTable workers={filtered} />
            </div>
          )}
        </div>
      </div>
      <AppFooter />
    </div>
  );
}

function WorkersTable({ workers }: { workers: Worker[] }) {
  const [sorting, setSorting] = useState<SortingState>([]);

  const columns: ColumnDef<Worker>[] = [
    {
      accessorKey: 'id',
      header: 'Worker',
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
      id: 'owner',
      header: 'Owner',
      cell: (info) => {
        const w = info.row.original;
        const ownerLabel =
          w.owner?.display_name ?? (w.owner?.handle ? `@${w.owner.handle}` : null) ?? 'Anonymous';
        const ownerStyle = w.owner
          ? { fontFamily: 'var(--font-serif)', fontSize: 14 }
          : { fontStyle: 'italic', color: 'var(--ink-500)' };
        const ownerColor = w.owner ? 'var(--ink-900)' : 'var(--ink-500)';
        return (
          <span style={ownerStyle}>
            <span style={{ color: ownerColor }}>{ownerLabel}</span>
          </span>
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
            {w.last_contribution_at ? formatRelative(w.last_contribution_at) : '—'}
          </span>
        );
      },
    },
    {
      id: 'lastSeen',
      header: 'Last seen',
      cell: (info) => {
        const w = info.row.original;
        return (
          <span className="num-cell" style={{ color: 'var(--ink-500)' }}>
            {formatRelative(w.last_seen)}
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
  );
}

function FilterTab({
  value,
  current,
  setFilter,
  children,
}: {
  value: StatusFilter;
  current: StatusFilter;
  setFilter: (v: StatusFilter) => void;
  children: React.ReactNode;
}) {
  return (
    <button
      type="button"
      className={`lead-tab ${current === value ? 'active' : ''}`}
      onClick={() => setFilter(value)}
    >
      {children}
    </button>
  );
}

function formatRelative(iso: string): string {
  const then = new Date(iso).getTime();
  const now = Date.now();
  const diff = Math.max(0, now - then);
  const sec = Math.floor(diff / 1000);
  if (sec < 60) return `${sec}s ago`;
  const min = Math.floor(sec / 60);
  if (min < 60) return `${min}m ago`;
  const hr = Math.floor(min / 60);
  if (hr < 24) return `${hr}h ago`;
  const day = Math.floor(hr / 24);
  if (day < 30) return `${day}d ago`;
  return new Date(iso).toLocaleDateString();
}
