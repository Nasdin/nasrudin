import { createFileRoute, Link } from '@tanstack/react-router';
import { HeroLiveTheorem } from '~/components/landing/HeroLiveTheorem';
import { AppFooter } from '~/components/platform/AppFooter';

export const Route = createFileRoute('/')({ component: Landing });

function Landing() {
  return (
    <div className="page">
      <header className="topbar">
        <div className="topbar-inner">
          <div className="brand">
            <span>
              Nasrud
              <span className="brand-dot" />
              in
            </span>
            <span className="brand-tag">Synthetic theorem · Lean 4</span>
          </div>
          <nav className="nav">
            {/* @ts-expect-error route added in Phase 8.x */}
            <Link to="/browse">Browse corpus</Link>
            {/* @ts-expect-error route added in Phase 8.x */}
            <Link to="/leaderboard">Contributors</Link>
            {/* @ts-expect-error route added in Phase 8.x */}
            <Link to="/api-docs">API</Link>
            {/* @ts-expect-error route added in Phase 8.x */}
            <Link to="/pricing">Pricing</Link>
            <span className="nav-sep" aria-hidden />
            <Link to="/signin" className="nav-secondary">
              Sign in
            </Link>
            <a href="#run" className="nav-cta">
              Run a worker →
            </a>
          </nav>
        </div>
      </header>
      <section className="hero">
        <div className="hero-pattern" />
        <div className="container-wide">
          <div className="hero-grid">
            <div>
              <div className="hero-eyebrow">
                <span className="eyebrow-dot" /> Distributed theorem-generation engine · v0.4
              </div>
              <h1 className="hero-title">
                Derive physics from <em>pure logic.</em>
              </h1>
              <p className="hero-sub">
                Nasrudin starts from mathematical axioms and physics postulates, then evolves new
                theorems with a genetic algorithm — formally proving every survivor in Lean&nbsp;4.
                Eventually, it rediscovers known physics. On its own.
              </p>
              <div className="hero-ctas">
                <a className="btn btn-primary" href="#run">
                  Run a worker node <span className="btn-arrow">→</span>
                </a>
                {/* @ts-expect-error route added in Phase 8.x */}
                <Link className="btn btn-secondary" to="/browse">
                  Browse the corpus
                </Link>
              </div>
            </div>
            <div>
              <div className="overline" style={{ marginBottom: 12 }}>
                Live · just verified
              </div>
              <HeroLiveTheorem />
            </div>
          </div>
        </div>
      </section>
      <AppFooter />
    </div>
  );
}
