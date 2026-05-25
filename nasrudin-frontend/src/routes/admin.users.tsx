import { createFileRoute, Link } from '@tanstack/react-router';
import { useQuery } from '@tanstack/react-query';
import { useState } from 'react';
import { adminFetch } from '~/lib/adminApi';
import DataTable from '~/components/admin/DataTable';
import type { AdminUser } from '~/lib/adminTypes';

interface ListResp {
  users: AdminUser[];
  total: number;
  page: number;
  page_size: number;
}

export const Route = createFileRoute('/admin/users')({ loader: async () => null, component: UsersList });

function UsersList() {
  const [search, setSearch] = useState('');
  const [page, setPage] = useState(1);
  const { data } = useQuery<ListResp>({
    queryKey: ['admin', 'users', page, search],
    queryFn: () =>
      adminFetch<ListResp>(
        `/api/admin/users?page=${page}&page_size=25&search=${encodeURIComponent(search)}`,
      ),
  });
  return (
    <section>
      <h1>Users{data ? ` (${data.total})` : ''}</h1>
      <input
        value={search}
        onChange={(e) => {
          setPage(1);
          setSearch(e.target.value);
        }}
        placeholder="Search by email or display name"
        style={{ width: 320, padding: 6, marginBottom: 12 }}
      />
      <DataTable
        columns={[
          {
            key: 'email',
            header: 'Email',
            render: (u) => (
              <Link to="/admin/users/$id" params={{ id: u.id }}>
                {u.email}
              </Link>
            ),
          },
          { key: 'plan_tier', header: 'Plan' },
          { key: 'research_credits', header: 'Credits' },
          {
            key: 'is_admin',
            header: 'Admin',
            render: (u) => (u.is_admin ? '✓' : ''),
          },
          {
            key: 'is_trusted',
            header: 'Trusted',
            render: (u) => (u.is_trusted ? '✓' : ''),
          },
          {
            key: 'created_at',
            header: 'Created',
            render: (u) => new Date(u.created_at).toLocaleDateString(),
          },
        ]}
        rows={data?.users ?? []}
      />
      <div style={{ marginTop: 12, display: 'flex', gap: 8 }}>
        <button disabled={page <= 1} onClick={() => setPage((p) => p - 1)}>
          Prev
        </button>
        <span>Page {page}</span>
        <button onClick={() => setPage((p) => p + 1)}>Next</button>
      </div>
    </section>
  );
}
