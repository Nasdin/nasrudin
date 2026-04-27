import { Link } from '@tanstack/react-router';

export function AppFooter() {
  return (
    <footer
      style={{
        background: 'var(--ink-900)',
        color: 'var(--paper-200)',
        padding: '40px 0',
        marginTop: 'auto',
      }}
    >
      <div
        className="container-wide"
        style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center',
          flexWrap: 'wrap',
          gap: 16,
        }}
      >
        <div style={{ display: 'flex', alignItems: 'baseline', gap: 16, fontSize: 13 }}>
          <span style={{ fontFamily: 'var(--font-serif)', fontSize: 18, color: 'var(--paper-50)' }}>
            Nasrud·in
          </span>
          <span style={{ color: 'var(--ink-300)' }}>v0.4.2 · Open source · MIT</span>
        </div>
        <div style={{ display: 'flex', gap: 24, fontSize: 13 }}>
          <Link to="/" style={{ color: 'var(--paper-200)', textDecoration: 'none' }}>
            Landing
          </Link>
          {/* @ts-expect-error route added in Phase 7+ */}
          <Link to="/api-docs" style={{ color: 'var(--paper-200)', textDecoration: 'none' }}>
            API
          </Link>
          {/* @ts-expect-error route added in Phase 7+ */}
          <Link to="/pricing" style={{ color: 'var(--paper-200)', textDecoration: 'none' }}>
            Pricing
          </Link>
          <a
            href="https://github.com"
            style={{ color: 'var(--paper-200)', textDecoration: 'none' }}
          >
            GitHub
          </a>
        </div>
      </div>
    </footer>
  );
}
