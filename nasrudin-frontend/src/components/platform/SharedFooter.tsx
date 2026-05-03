import { Link } from '@tanstack/react-router';
import { useLandingStats } from '~/lib/queries';

export function SharedFooter() {
  const { data: stats } = useLandingStats();
  const verified = stats?.verified_theorems;
  const workers = stats?.active_workers;

  return (
    <footer className="site-footer">
      <div className="container-wide site-footer-inner">
        <div className="site-footer-row">
          <span className="site-footer-tag">
            Nasrud<span className="brand-dot" />in · open by principle · MIT-licensed core
          </span>
          <Link to="/sponsor" className="site-footer-donate">
            ♥ Donate to keep the corpus free →
          </Link>
          <span className="site-footer-version">
            v0.4.2
            {verified != null && ` · ${verified.toLocaleString()} theorems`}
            {workers != null && ` · ${workers} workers live`}
          </span>
        </div>
        <div className="site-footer-row site-footer-row-links">
          <nav className="site-footer-links" aria-label="Footer">
            <a href="https://github.com/nasdin/nasrudin">GitHub</a>
            <Link to="/api-docs">API</Link>
            <Link to="/pricing">Pricing</Link>
            <Link to="/sponsor">Sponsor</Link>
            <Link to="/leaderboard">Contributors</Link>
            <a href="mailto:nasrudinsalim@nasrudin.org">nasrudinsalim@nasrudin.org</a>
          </nav>
        </div>
        <div className="site-footer-row site-footer-row-credit">
          <span className="site-footer-credit">
            Designed &amp; built by{' '}
            <strong>Nasrudin Bin Salim</strong>.
          </span>
          <span className="site-footer-credit site-footer-credit-mono">
            Powered by <strong>Replikate Labs Pte Ltd</strong> · Singapore 🇸🇬
          </span>
        </div>
      </div>
    </footer>
  );
}
