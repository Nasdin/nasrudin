import { createFileRoute, Link } from '@tanstack/react-router';
import { useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useWorkers } from '~/lib/queries';
import type { Worker } from '~/lib/types';

export const Route = createFileRoute('/workers')({ component: WorkersPage });

type StatusFilter = 'all' | 'active' | 'inactive' | 'disconnected';

function WorkersPage() {
  const { data, isPending } = useWorkers();
  const [filter, setFilter] = useState<StatusFilter>('all');
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

        <div
          className="stat-row"
          style={{ marginTop: 24, marginBottom: 32, gridTemplateColumns: 'repeat(3, 1fr)' }}
        >
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
            <table className="lead-table">
              <thead>
                <tr>
                  <th>Worker</th>
                  <th>Owner</th>
                  <th>Host</th>
                  <th style={{ textAlign: 'right' }}>Status</th>
                  <th style={{ textAlign: 'right' }}>Theorems</th>
                  <th style={{ textAlign: 'right' }}>Last verified</th>
                  <th style={{ textAlign: 'right' }}>Last seen</th>
                </tr>
              </thead>
              <tbody>
                {filtered.map((w) => (
                  <WorkerRow key={w.id} w={w} />
                ))}
              </tbody>
            </table>
          )}
        </div>
      </div>
      <AppFooter />
    </div>
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

function WorkerRow({ w }: { w: Worker }) {
  const status = String(w.status).toLowerCase();
  const ownerLabel =
    w.owner?.display_name ?? (w.owner?.handle ? `@${w.owner.handle}` : null) ?? 'Anonymous';
  const ownerColor = w.owner ? 'var(--ink-900)' : 'var(--ink-500)';
  const ownerStyle: React.CSSProperties = w.owner
    ? { fontFamily: 'var(--font-serif)', fontSize: 14 }
    : { fontStyle: 'italic', color: 'var(--ink-500)' };
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
      <td style={ownerStyle}>
        <span style={{ color: ownerColor }}>{ownerLabel}</span>
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
      <td className="num-cell">{w.theorems_contributed.toLocaleString()}</td>
      <td className="num-cell" style={{ color: 'var(--ink-500)' }}>
        {w.last_contribution_at ? formatRelative(w.last_contribution_at) : '—'}
      </td>
      <td className="num-cell" style={{ color: 'var(--ink-500)' }}>
        {formatRelative(w.last_seen)}
      </td>
    </tr>
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
