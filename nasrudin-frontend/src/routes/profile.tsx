import { createFileRoute, Link, redirect } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { bytesToHex } from '~/lib/hex';
import {
  useApiKeys,
  useLogout,
  useMe,
  useMeProfile,
  useMeStats,
  useMyWorkers,
  useSavedSearches,
} from '~/lib/queries';

export const Route = createFileRoute('/profile')({ component: ProfilePage });

function ProfilePage() {
  const { data: me, isPending } = useMe();
  const { data: stats } = useMeStats();
  const { data: keys } = useApiKeys();
  const { data: saved } = useSavedSearches();
  const { data: profile } = useMeProfile();
  const { data: myWorkers } = useMyWorkers();
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

  const displayName = profile?.display_name ?? me.display_name ?? me.email;
  const handle = profile?.profile?.handle ?? `@${me.email.split('@')[0]}`;
  const institution = profile?.profile?.institution;
  const field = profile?.profile?.field;
  const bio = profile?.profile?.bio;
  const initials = displayName
    .split(/\s+/)
    .map((w) => w[0])
    .join('')
    .slice(0, 2)
    .toUpperCase();

  const handleLine = [handle.startsWith('@') ? handle : `@${handle}`, institution, field]
    .filter(Boolean)
    .join(' · ');

  const workers = myWorkers?.workers ?? [];
  const savedSearches = saved?.saved_searches ?? [];
  const recentTheorems = stats?.theorems_recent ?? [];

  return (
    <div className="app">
      <AppHeader active="profile" />
      <div className="container-wide">
        <div className="profile-head">
          <div className="profile-avatar">{initials}</div>
          <div>
            <h1 className="profile-name">{displayName}</h1>
            <div className="profile-handle">{handleLine}</div>
            {bio ? (
              <p className="profile-bio">{bio}</p>
            ) : (
              <p className="profile-bio" style={{ color: 'var(--ink-500)', fontStyle: 'italic' }}>
                No bio yet — <Link to="/settings">add one in settings →</Link>
              </p>
            )}
          </div>
          <div className="profile-tier">
            <div className="tier-pill">★ Researcher</div>
            <div style={{ marginTop: 12, fontSize: 12, color: 'var(--ink-500)' }}>
              Member since {new Date(me.created_at).toLocaleDateString()}
            </div>
            <Link to="/settings" style={{ fontSize: 12, marginTop: 6, display: 'inline-block' }}>
              Edit profile →
            </Link>
          </div>
        </div>

        <div className="stat-row">
          <div className="stat-cell">
            <div className="label">Saved searches</div>
            <div className="num">{stats?.saved_searches ?? 0}</div>
            <div className="delta">in library</div>
          </div>
          <div className="stat-cell">
            <div className="label">Active API keys</div>
            <div className="num">{stats?.api_keys ?? 0}</div>
            <div className="delta">
              <Link to="/api-keys">manage →</Link>
            </div>
          </div>
          <div className="stat-cell">
            <div className="label">My workers</div>
            <div className="num">{workers.length}</div>
            <div className="delta">
              {workers.filter((w) => String(w.status).toLowerCase() === 'active').length} active
            </div>
          </div>
          <div className="stat-cell">
            <div className="label">Theorems contributed</div>
            <div className="num">{(stats?.theorems_total ?? 0).toLocaleString()}</div>
            <div className="delta">across all workers</div>
          </div>
        </div>

        <div className="profile-grid">
          <div>
            <h3 className="section-h">My library</h3>
            {savedSearches.length === 0 && recentTheorems.length === 0 ? (
              <p style={{ color: 'var(--ink-500)' }}>
                Nothing saved yet — <Link to="/browse">browse the corpus →</Link>
              </p>
            ) : (
              <ul className="saved-list">
                {savedSearches.slice(0, 6).map((s) => (
                  <li key={s.id}>
                    <span className="saved-stmt">{s.label ?? s.latex}</span>
                    <span className="saved-domain">search</span>
                    <span className="saved-date">
                      {new Date(s.created_at).toLocaleDateString()}
                    </span>
                  </li>
                ))}
                {recentTheorems.slice(0, 6).map((t) => {
                  const id = bytesToHex(t.id);
                  return (
                    <li key={id}>
                      <Link
                        to="/theorem/$id"
                        params={{ id }}
                        style={{ textDecoration: 'none', color: 'inherit' }}
                      >
                        <span className="saved-stmt">{t.latex ?? t.canonical_statement}</span>
                      </Link>
                      <span className="saved-domain">{t.domain}</span>
                      <span className="saved-date">
                        {new Date(t.created_at).toLocaleDateString()}
                      </span>
                    </li>
                  );
                })}
              </ul>
            )}
            <Link to="/library" style={{ display: 'inline-block', marginTop: 16, fontSize: 13 }}>
              See full library →
            </Link>

            <div className="targeted-search-card">
              <div>
                <h4>Run a targeted search</h4>
                <p>Point the GA at a conjecture and let it search.</p>
              </div>
              <Link to="/browse" className="btn btn-primary">
                New search →
              </Link>
            </div>
          </div>

          <div>
            <h3 className="section-h">My workers</h3>
            {workers.length === 0 ? (
              <p style={{ color: 'var(--ink-500)' }}>
                No workers yet — <Link to="/api-keys">create a worker key →</Link>
              </p>
            ) : (
              <ul className="saved-list">
                {workers.map((w) => {
                  const status = String(w.status).toLowerCase();
                  return (
                    <li key={w.id}>
                      <span
                        className="saved-stmt"
                        style={{
                          fontFamily: 'var(--font-serif)',
                          fontStyle: 'normal',
                          fontSize: 15,
                        }}
                      >
                        {w.id}
                      </span>
                      <span
                        className="saved-domain"
                        style={{
                          color: status === 'active' ? 'var(--olive-700)' : 'var(--ink-500)',
                        }}
                      >
                        {status} · {w.theorems_contributed.toLocaleString()} thm
                      </span>
                      <span className="saved-date">
                        {w.last_contribution_at
                          ? new Date(w.last_contribution_at).toLocaleDateString()
                          : new Date(w.last_seen).toLocaleDateString()}
                      </span>
                    </li>
                  );
                })}
              </ul>
            )}
            <Link to="/workers" style={{ display: 'inline-block', marginTop: 16, fontSize: 13 }}>
              See all platform workers →
            </Link>

            <h3 className="section-h" style={{ marginTop: 32 }}>
              My API keys
            </h3>
            {(keys?.keys ?? []).length === 0 ? (
              <p style={{ color: 'var(--ink-500)' }}>
                No keys yet — <Link to="/api-keys">create one →</Link>
              </p>
            ) : (
              <ul className="saved-list">
                {keys?.keys.slice(0, 5).map((k) => (
                  <li key={k.id}>
                    <span
                      className="saved-stmt"
                      style={{
                        fontFamily: 'var(--font-serif)',
                        fontStyle: 'normal',
                        fontSize: 15,
                      }}
                    >
                      {k.name}
                    </span>
                    <span className="saved-domain">{k.kind}</span>
                    <span className="saved-date">
                      {k.last_used_at
                        ? `used ${new Date(k.last_used_at).toLocaleDateString()}`
                        : 'unused'}
                    </span>
                  </li>
                ))}
              </ul>
            )}
            <Link to="/api-keys" style={{ display: 'inline-block', marginTop: 16, fontSize: 13 }}>
              Manage all keys →
            </Link>
          </div>
        </div>

        <div style={{ marginTop: 64, paddingBottom: 32 }}>
          <button type="button" className="btn btn-secondary" onClick={() => logout.mutate()}>
            {logout.isPending ? 'Signing out…' : 'Sign out'}
          </button>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}
