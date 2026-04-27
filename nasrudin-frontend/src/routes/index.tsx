import { createFileRoute, Link } from '@tanstack/react-router';
import { GAViz } from '~/components/landing/GAViz';
import { HeroLiveTheorem } from '~/components/landing/HeroLiveTheorem';
import { InstallNode } from '~/components/landing/InstallNode';
import { PipelineDiagram } from '~/components/landing/PipelineDiagram';
import { RediscoveryGrid } from '~/components/landing/RediscoveryGrid';
import { WorkerMap } from '~/components/landing/WorkerMap';
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
            <Link to="/browse">Browse corpus</Link>
            <Link to="/leaderboard">Contributors</Link>
            <Link to="/api-docs">API</Link>
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
      <section className="section" id="how">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 01 / 04</div>
            <div className="section-title-block">
              <span className="overline">The pipeline</span>
              <h2 className="section-title">
                Five stages, one rule:{' '}
                <em>nothing enters the corpus that Lean&nbsp;4 hasn't proved twice.</em>
              </h2>
            </div>
          </div>
          <PipelineDiagram />
        </div>
      </section>
      <section className="section compact">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 02 / 04</div>
            <div className="section-title-block">
              <span className="overline">Inside one cycle</span>
              <h2 className="section-title">
                Watch the GA <em>arrive at Newton</em> — without being told.
              </h2>
            </div>
          </div>
          <GAViz />
        </div>
      </section>
      <section className="section" id="discoveries">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 03 / 04</div>
            <div className="section-title-block">
              <span className="overline">Featured rediscoveries</span>
              <h2 className="section-title">
                Physics that <em>found itself</em> — and physics still in the dark.
              </h2>
            </div>
          </div>
          <RediscoveryGrid />
        </div>
      </section>
      <section className="section" id="network">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 04 / 04</div>
            <div className="section-title-block">
              <span className="overline">The network</span>
              <h2 className="section-title">
                A distributed prover, <em>built from home PCs and cloud nodes.</em>
              </h2>
            </div>
          </div>
          <WorkerMap />
        </div>
      </section>
      <section className="section" id="run">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 05 / 05</div>
            <div className="section-title-block">
              <span className="overline">Contribute compute</span>
              <h2 className="section-title">
                Run a worker. <em>Help physics rediscover itself.</em>
              </h2>
            </div>
          </div>
          <InstallNode />
        </div>
      </section>
      <AppFooter />
    </div>
  );
}
