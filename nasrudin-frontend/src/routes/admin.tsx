import { useQuery } from '@tanstack/react-query';
import { createFileRoute, Link, Outlet } from '@tanstack/react-router';
import ImpersonationBanner from '~/components/admin/ImpersonationBanner';
import { SignInPrompt } from '~/components/platform/SignInPrompt';
import { ApiError, apiFetch } from '~/lib/api';
import { useMe } from '~/lib/queries';

export const Route = createFileRoute('/admin')({ loader: async () => null, component: AdminGate });

type AdminAccess = 'admin' | 'not_admin';

/// Probes a cheap admin endpoint to distinguish admin (200) from
/// not-admin (403). Uses raw `apiFetch` (not `adminFetch`) so we hit
/// the real user — `adminFetch` threads the impersonation token AND
/// hard-redirects to `/` on 403, both of which would defeat this gate.
function useAdminAccess(enabled: boolean) {
  return useQuery<AdminAccess>({
    queryKey: ['admin', 'access'],
    enabled,
    queryFn: async () => {
      try {
        await apiFetch<unknown>('/api/admin/users?page=1&page_size=1');
        return 'admin';
      } catch (e) {
        if (e instanceof ApiError && e.status === 403) return 'not_admin';
        throw e;
      }
    },
    staleTime: 60_000,
    retry: false,
  });
}

function AdminGate() {
  const { data: me, isPending: mePending } = useMe();
  const { data: access, isPending: accessPending } = useAdminAccess(!!me);

  if (mePending) return <p style={{ padding: 24 }}>…</p>;

  if (!me) {
    return (
      <SignInPrompt
        overline="Admin"
        title="Admin panel"
        description="Sign in with your admin account to manage users, audit logs, bulk runs, steering, and the corpus."
      />
    );
  }

  if (accessPending) return <p style={{ padding: 24 }}>Checking admin access…</p>;

  if (access !== 'admin') {
    return (
      <div className="app">
        <div className="container-wide" style={{ maxWidth: 720, padding: 64, textAlign: 'center' }}>
          <span className="overline">Admin</span>
          <h1>Not authorized</h1>
          <p style={{ color: 'var(--ink-700)' }}>
            <strong>{me.email}</strong> doesn't have admin access on this instance.
          </p>
          <p style={{ marginTop: 24 }}>
            <Link to="/" className="btn btn-ghost">
              Back to home
            </Link>
          </p>
        </div>
      </div>
    );
  }

  return <AdminLayout />;
}

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
