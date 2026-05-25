import { createFileRoute, Link } from '@tanstack/react-router';
import {
  flexRender,
  getCoreRowModel,
  useReactTable,
  type ColumnDef,
  type SortingState,
} from '@tanstack/react-table';
import { useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useContributorWorkers } from '~/lib/queries';
import type { Worker } from '~/lib/types';

export const Route = createFileRoute('/contributors/$id')({
  loader: async () => null,
  component: ContributorDetailPage,
});

function ContributorDetailPage() {
  const { id } = Route.useParams();
  const { data: workers, isPending } = useContributorWorkers(id);
  const [sorting, setSorting] = useState<SortingState>([]);

  const totalThm = workers?.reduce((s, w) => s + w.theorems_contributed, 0) ?? 0;
  const active = workers?.filter((w) => String(w.status).toLowerCase() === 'active').length ?? 0;

  return (
    <div className="app">
      <AppHeader active="leader" />
      <div className="container-wide">
        <div className="page-head">
          <Link to="/leaderboard" style={{ color: 'var(--ink-500)', textDecoration: 'none' }}>
            ← Back to contributors
          </Link>
          <h1 style={{ marginTop: 16 }}>
            Workers for contributor
          </h1>
          <p className="lede">
            All workers owned by this contributor, ordered by theorems contributed.
          </p>
        </div>

        <div className="stat-row stat-row-3" style={{ marginTop: 24, marginBottom: 32 }}>
          <div className="stat-cell">
            <div className="label">Workers · total</div>
            <div className="num">{workers?.length ?? 0}</div>
            <div className="delta">{active} active</div>
          </div>
          <div className="stat-cell">
            <div className="label">Theorems contributed</div>
            <div className="num">{totalThm.toLocaleString()}</div>
            <div className="delta">across all workers</div>
          </div>
          <div className="stat-cell">
            <div className="label">Contributor ID</div>
            <div className="num" style={{ fontSize: 14, fontFamily: 'var(--font-mono)' }}>
              {id}
            </div>
            <div className="delta">unique identifier</div>
          </div>
        </div>

        {isPending && <p style={{ color: 'var(--ink-500)' }}>loading…</p>}
        {!isPending && (!workers || workers.length === 0) && (
          <p style={{ color: 'var(--ink-500)', padding: 32 }}>
            No workers found for this contributor.
          </p>
        )}
        {workers && workers.length > 0 && (
          <div className="lead-table-scroll">
            <WorkersTable workers={workers} sorting={sorting} setSorting={setSorting} />
          </div>
        )}
      </div>
      <AppFooter />
    </div>
  );
}

function WorkersTable({
  workers,
  sorting,
  setSorting,
}: {
  workers: Worker[];
  sorting: SortingState;
  setSorting: (s: SortingState | ((prev: SortingState) => SortingState)) => void;
}) {
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
                {header.isPlaceholder
                  ? null
                  : flexRender(header.column.columnDef.header, header.getContext())}
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
