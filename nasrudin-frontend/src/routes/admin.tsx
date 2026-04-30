import { createFileRoute, Link, Outlet, redirect } from '@tanstack/react-router';
import { ApiError } from '~/lib/api';
import { adminFetch } from '~/lib/adminApi';
import ImpersonationBanner from '~/components/admin/ImpersonationBanner';

export const Route = createFileRoute('/admin')({
  beforeLoad: async () => {
    try {
      await adminFetch<unknown>('/api/admin/users?page=1&page_size=1');
    } catch (e) {
      if (e instanceof ApiError && (e.status === 401 || e.status === 403)) {
        throw redirect({ to: '/' });
      }
      throw e;
    }
  },
  component: AdminLayout,
});

function AdminLayout() {
  return (
    <div>
      <ImpersonationBanner />
      <div style={{ display: 'flex', minHeight: '100vh' }}>
        <aside
          style={{
            width: 200,
            padding: 16,
            borderRight: '1px solid var(--paper-300)',
            background: 'var(--paper-50)',
          }}
        >
          <h1 style={{ marginTop: 0, fontSize: 18 }}>Admin</h1>
          <nav style={{ display: 'flex', flexDirection: 'column', gap: 6 }}>
            <Link to="/admin">Dashboard</Link>
            <Link to="/admin/users">Users</Link>
            <Link to="/admin/audit">Audit log</Link>
            <Link to="/admin/bulk">Bulk runs</Link>
            <Link to="/admin/steering">Steering</Link>
            <Link to="/admin/corpus">Corpus</Link>
          </nav>
        </aside>
        <main style={{ flex: 1, padding: 24 }}>
          <Outlet />
        </main>
      </div>
    </div>
  );
}
