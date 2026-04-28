import { Link } from '@tanstack/react-router';
import { useMe } from '~/lib/queries';

const NAV = [
  { to: '/search', label: 'Search', key: 'search' },
  { to: '/browse', label: 'Browse corpus', key: 'browse' },
  { to: '/library', label: 'My library', key: 'library' },
  { to: '/workers', label: 'Workers', key: 'workers' },
  { to: '/leaderboard', label: 'Contributors', key: 'leader' },
  { to: '/api-docs', label: 'API & data', key: 'api' },
  { to: '/api-keys', label: 'API keys', key: 'api-keys' },
  { to: '/pricing', label: 'Pricing', key: 'pricing' },
] as const;

export function AppHeader({ active }: { active?: string }) {
  const { data: me } = useMe();
  return (
    <>
      <header className="app-header">
        <div className="app-header-inner">
          <Link to="/" className="app-brand">
            <span>
              Nasrud
              <span className="brand-dot" />
              in
            </span>
          </Link>
          <div className="app-search">
            <svg
              width="14"
              height="14"
              viewBox="0 0 24 24"
              fill="none"
              stroke="currentColor"
              strokeWidth="1.8"
              strokeLinecap="round"
              strokeLinejoin="round"
              aria-hidden="true"
            >
              <circle cx="11" cy="11" r="7" />
              <path d="m21 21-4.3-4.3" />
            </svg>
            <span>Search theorems · names · Lean tactics</span>
            <kbd>⌘K</kbd>
          </div>
          <div className="app-actions">
            <Link to="/pricing" className="app-nav-link">
              Pricing
            </Link>
            <Link to="/api-docs" className="app-nav-link">
              API
            </Link>
            {me ? (
              <Link to="/profile" className="app-avatar" title={me.email}>
                {(me.display_name ?? me.email).slice(0, 2).toUpperCase()}
              </Link>
            ) : (
              <Link to="/signin" className="app-nav-link">
                Sign in
              </Link>
            )}
          </div>
        </div>
      </header>
      <nav className="app-subnav">
        <div className="app-subnav-inner">
          {NAV.map((n) => (
            <Link key={n.key} to={n.to} className={active === n.key ? 'active' : ''}>
              {n.label}
            </Link>
          ))}
        </div>
      </nav>
    </>
  );
}
