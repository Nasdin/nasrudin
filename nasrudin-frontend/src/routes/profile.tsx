import { createFileRoute, Link, redirect } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { useApiKeys, useLogout, useMe, useMeStats, useSavedSearches } from '~/lib/queries';

export const Route = createFileRoute('/profile')({ component: ProfilePage });

function ProfilePage() {
  const { data: me, isPending } = useMe();
  const { data: stats } = useMeStats();
  const { data: keys } = useApiKeys();
  const { data: saved } = useSavedSearches();
  const logout = useLogout();

  if (isPending)
    return (
      <div className="container-wide" style={{ padding: 64 }}>
        …
      </div>
    );
  if (!me) {
    throw redirect({ to: '/signin' });
  }
  return (
    <div className="app">
      <AppHeader active="profile" />
      <div className="container-wide">
        <div className="profile-head">
          <div className="profile-avatar">
            {(me.display_name ?? me.email).slice(0, 2).toUpperCase()}
          </div>
          <div>
            <h1 className="profile-name">{me.display_name ?? me.email}</h1>
            <div className="profile-handle">{me.email}</div>
          </div>
          <div className="profile-tier">
            <div className="tier-pill">★ Researcher</div>
            {/* @ts-expect-error route added in Phase 8 */}
            <Link to="/pricing" style={{ fontSize: 12, marginTop: 6, display: 'inline-block' }}>
              Manage billing →
            </Link>
          </div>
        </div>

        <div className="stat-row">
          <div className="stat-cell">
            <div className="label">Saved searches</div>
            <div className="num">{stats?.saved_searches ?? 0}</div>
          </div>
          <div className="stat-cell">
            <div className="label">Active API keys</div>
            <div className="num">{stats?.api_keys ?? 0}</div>
          </div>
          <div className="stat-cell">
            <div className="label">Member since</div>
            <div className="num" style={{ fontSize: 24 }}>
              {new Date(me.created_at).toLocaleDateString()}
            </div>
          </div>
          <div className="stat-cell">
            <div className="label">Citations made</div>
            <div className="num">—</div>
          </div>
        </div>

        <div className="profile-grid">
          <div>
            <h3 className="section-h">Saved searches</h3>
            {(saved?.saved_searches ?? []).length === 0 ? (
              <p style={{ color: 'var(--ink-500)' }}>You haven't saved any searches yet.</p>
            ) : (
              <ul className="saved-list">
                {saved?.saved_searches.map((s) => (
                  <li key={s.id}>
                    <span className="saved-stmt">{s.label ?? s.latex}</span>
                    <span className="saved-date">
                      {new Date(s.created_at).toLocaleDateString()}
                    </span>
                  </li>
                ))}
              </ul>
            )}
          </div>
          <div>
            <h3 className="section-h">API keys</h3>
            {(keys?.keys ?? []).length === 0 ? (
              <p style={{ color: 'var(--ink-500)' }}>
                {/* @ts-expect-error route added in Phase 7.3 */}
                No keys yet — <Link to="/api-keys">create one →</Link>
              </p>
            ) : (
              <ul className="saved-list">
                {keys?.keys.map((k) => (
                  <li key={k.id}>
                    <span className="saved-stmt">{k.name}</span>
                    <span className="saved-domain" style={{ fontFamily: 'var(--font-mono)' }}>
                      {k.prefix}…
                    </span>
                    <span className="saved-date">
                      {new Date(k.created_at).toLocaleDateString()}
                    </span>
                  </li>
                ))}
              </ul>
            )}
            {/* @ts-expect-error route added in Phase 7.3 */}
            <Link to="/api-keys" style={{ display: 'inline-block', marginTop: 16 }}>
              Manage all keys →
            </Link>
          </div>
        </div>

        <div style={{ marginTop: 64 }}>
          <button type="button" className="btn btn-secondary" onClick={() => logout.mutate()}>
            {logout.isPending ? 'Signing out…' : 'Sign out'}
          </button>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}
