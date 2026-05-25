import { createFileRoute } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { adminFetch } from '~/lib/adminApi';

export const Route = createFileRoute('/admin/steering')({ loader: async () => null, component: SteeringPage });

function SteeringPage() {
  const { data } = useQuery<unknown>({
    queryKey: ['admin', 'steering'],
    queryFn: () => adminFetch<unknown>('/api/admin/steering/recent'),
    refetchInterval: 30_000,
  });
  return (
    <section>
      <h1>Cluster steering — recent cycles</h1>
      <pre style={{ background: 'var(--paper-100)', padding: 12, overflowX: 'auto' }}>
        {JSON.stringify(data, null, 2)}
      </pre>
    </section>
  );
}
