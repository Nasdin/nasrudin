import { createFileRoute } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { adminFetch } from '~/lib/adminApi';
import DataTable from '~/components/admin/DataTable';
import type { AuditEntry } from '~/lib/adminTypes';

export const Route = createFileRoute('/admin/audit')({ loader: async () => null, component: AuditPage });

function AuditPage() {
  const { data } = useQuery<{ entries: AuditEntry[] }>({
    queryKey: ['admin', 'audit'],
    queryFn: () => adminFetch<{ entries: AuditEntry[] }>('/api/admin/audit?limit=200'),
  });
  return (
    <section>
      <h1>Audit log</h1>
      <DataTable
        columns={[
          {
            key: 'created_at',
            header: 'When',
            render: (r) => new Date(r.created_at).toLocaleString(),
          },
          { key: 'action', header: 'Action' },
          { key: 'actor_user_id', header: 'Actor' },
          { key: 'target_user_id', header: 'Target' },
          { key: 'reason', header: 'Reason' },
        ]}
        rows={data?.entries ?? []}
      />
    </section>
  );
}
