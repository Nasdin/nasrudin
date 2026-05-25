import { createFileRoute } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { adminFetch } from '~/lib/adminApi';
import type { AdminStats } from '~/lib/adminTypes';

export const Route = createFileRoute('/admin/')({ loader: async () => null, component: AdminDashboard });

function AdminDashboard() {
  const { data } = useQuery<AdminStats>({
    queryKey: ['admin', 'stats'],
    queryFn: () => adminFetch<AdminStats>('/api/admin/stats'),
    refetchInterval: 15_000,
  });
  if (!data) return <p>Loading…</p>;
  return (
    <section>
      <h1>Dashboard</h1>
      <div style={{ display: 'grid', gridTemplateColumns: 'repeat(3, 1fr)', gap: 16 }}>
        <Card label="Users (total)" value={data.users_total} />
        <Card label="Admins" value={data.admins_count} />
        <Card label="Trusted users" value={data.trusted_users} />
        <Card label="Reverify depth" value={data.reverify_queue_depth} />
        <Card label="Lake-promotion depth" value={data.lake_promotion_queue_depth} />
      </div>
      <h2 style={{ marginTop: 32 }}>Theorems by status</h2>
      <pre style={{ background: 'var(--paper-100)', padding: 12, overflowX: 'auto' }}>
        {JSON.stringify(data.theorems_by_status, null, 2)}
      </pre>
      <h2>Recent audit log</h2>
      <pre style={{ background: 'var(--paper-100)', padding: 12, overflowX: 'auto' }}>
        {JSON.stringify(data.recent_audit, null, 2)}
      </pre>
    </section>
  );
}

function Card({ label, value }: { label: string; value: number | string }) {
  return (
    <div style={{ padding: 16, background: 'var(--paper-100)', borderRadius: 8 }}>
      <div style={{ fontSize: 12, color: 'var(--ink-500)' }}>{label}</div>
      <div style={{ fontSize: 24, fontWeight: 600 }}>{String(value)}</div>
    </div>
  );
}
