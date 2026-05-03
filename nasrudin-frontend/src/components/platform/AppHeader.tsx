import { Link, useRouterState } from '@tanstack/react-router';
import { useLandingStats, useMe } from '~/lib/queries';

export type SectionKey =
  | 'corpus'
  | 'discoveries'
  | 'network'
  | 'workspace'
  | 'build'
  | 'pricing';

type SubTab = { to: string; label: string; key: string; auth?: boolean };
type Section = {
  key: SectionKey;
  label: string;
  to: string;
  pill?: 'NEW';
  auth?: boolean;
  sub?: SubTab[];
};

// New consolidated IA — 6 top-level sections (down from 10 nav items).
// Each section can declare a list of sub-tabs that render in a second
// row when that section is active.
const SECTIONS: Section[] = [
  {
    key: 'corpus',
    label: 'Corpus',
    to: '/browse',
    sub: [
      { to: '/browse', label: 'Browse', key: 'browse' },
      { to: '/search', label: 'Search by name', key: 'search' },
      { to: '/search/concept', label: 'Concept search', key: 'concept' },
    ],
  },
  { key: 'discoveries', label: 'Discoveries', to: '/discoveries', pill: 'NEW' },
  {
    key: 'network',
    label: 'Network',
    to: '/leaderboard',
    sub: [
      { to: '/leaderboard', label: 'Contributors', key: 'leaderboard' },
      { to: '/workers', label: 'Workers', key: 'workers' },
    ],
  },
  {
    key: 'workspace',
    label: 'Workspace',
    to: '/library',
    auth: true,
    sub: [
      { to: '/library', label: 'Library', key: 'library' },
      { to: '/research', label: 'Targeted runs', key: 'research' },
      { to: '/conjecture', label: 'New conjecture', key: 'conjecture' },
      { to: '/jobs', label: 'Job history', key: 'jobs' },
    ],
  },
  {
    key: 'build',
    label: 'Build',
    to: '/api-docs',
    sub: [
      { to: '/api-docs', label: 'API reference', key: 'api-docs' },
      { to: '/api-keys', label: 'My API keys', key: 'api-keys' },
    ],
  },
  { key: 'pricing', label: 'Pricing', to: '/pricing' },
];

// Lets existing call sites pass either the old 10-key value (search,
// browse, library, conjecture, …) or the new section key. Both resolve
// to one of the six sections.
const ACTIVE_TO_SECTION: Record<string, SectionKey> = {
  search: 'corpus',
  browse: 'corpus',
  concept: 'corpus',
  corpus: 'corpus',
  discoveries: 'discoveries',
  workers: 'network',
  leader: 'network',
  leaderboard: 'network',
  contributors: 'network',
  network: 'network',
  library: 'workspace',
  conjecture: 'workspace',
  research: 'workspace',
  jobs: 'workspace',
  workspace: 'workspace',
  api: 'build',
  'api-docs': 'build',
  'api-keys': 'build',
  build: 'build',
  pricing: 'pricing',
};

// Path-based fallback so any route gets the right section highlighted
// without having to thread a prop through every page.
function sectionFromPath(pathname: string): SectionKey | null {
  if (pathname.startsWith('/discoveries')) return 'discoveries';
  if (pathname.startsWith('/browse') || pathname.startsWith('/search')) return 'corpus';
  if (pathname.startsWith('/workers') || pathname.startsWith('/leaderboard') || pathname.startsWith('/contributors')) return 'network';
  if (pathname.startsWith('/library') || pathname.startsWith('/conjecture') || pathname.startsWith('/research') || pathname.startsWith('/jobs')) return 'workspace';
  if (pathname.startsWith('/api-docs') || pathname.startsWith('/api-keys')) return 'build';
  if (pathname.startsWith('/pricing')) return 'pricing';
  return null;
}

function subFromPath(pathname: string): string | null {
  if (pathname.startsWith('/search/concept')) return 'concept';
  if (pathname.startsWith('/search')) return 'search';
  if (pathname.startsWith('/browse')) return 'browse';
  if (pathname.startsWith('/leaderboard') || pathname.startsWith('/contributors')) return 'leaderboard';
  if (pathname.startsWith('/workers')) return 'workers';
  if (pathname.startsWith('/library')) return 'library';
  if (pathname.startsWith('/conjecture')) return 'conjecture';
  if (pathname.startsWith('/research')) return 'research';
  if (pathname.startsWith('/jobs')) return 'jobs';
  if (pathname.startsWith('/api-docs')) return 'api-docs';
  if (pathname.startsWith('/api-keys')) return 'api-keys';
  return null;
}

function LivePulse() {
  const { data } = useLandingStats();
  const verified = data?.verified_24h;
  return (
    <div className="app-pulse" title="Live verification feed">
      <span className="pulse-dot" />
      <span>
        <strong>{verified != null ? verified.toLocaleString() : '—'}</strong>{' '}
        verified · last 24h
      </span>
    </div>
  );
}

export function AppHeader({ active }: { active?: string } = {}) {
  const { data: me } = useMe();
  const pathname = useRouterState({ select: (s) => s.location.pathname });
  const sectionKey = (active && ACTIVE_TO_SECTION[active]) ?? sectionFromPath(pathname);
  const subKey = subFromPath(pathname);
  const activeSection = SECTIONS.find((s) => s.key === sectionKey);

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
          <Link to="/search" className="app-search" title="Search (⌘K)">
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
            <span className="app-search-placeholder">
              Search theorems · names · Lean tactics
            </span>
            <kbd>⌘K</kbd>
          </Link>
          <div className="app-actions">
            <LivePulse />
            <Link to="/sponsor" className="app-donate-btn">
              ♥ Donate
            </Link>
            {me ? (
              <Link to="/profile" className="app-avatar" title={me.email}>
                {(me.display_name ?? me.email).slice(0, 2).toUpperCase()}
              </Link>
            ) : (
              <Link to="/signin" className="app-nav-link">
                Sign in →
              </Link>
            )}
          </div>
        </div>
      </header>
      <nav className="app-subnav">
        <div className="app-subnav-inner">
          {SECTIONS.filter((s) => !s.auth || me).map((s) => (
            <Link
              key={s.key}
              to={s.to}
              className={sectionKey === s.key ? 'active' : ''}
            >
              {s.label}
              {s.pill && <span className="nav-pill">{s.pill}</span>}
            </Link>
          ))}
        </div>
      </nav>
      {activeSection?.sub && activeSection.sub.length > 1 && (
        <nav className="app-subtabs">
          <div className="app-subtabs-inner">
            {activeSection.sub
              .filter((t) => !t.auth || me)
              .map((t) => (
                <Link
                  key={t.key}
                  to={t.to}
                  className={subKey === t.key ? 'active' : ''}
                >
                  {t.label}
                </Link>
              ))}
          </div>
        </nav>
      )}
    </>
  );
}
