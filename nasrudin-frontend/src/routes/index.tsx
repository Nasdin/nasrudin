import { createFileRoute, Link } from '@tanstack/react-router';
import { GAViz } from '~/components/landing/GAViz';
import { HeroLiveTheorem } from '~/components/landing/HeroLiveTheorem';
import { InstallNode } from '~/components/landing/InstallNode';
import { LandingFooter } from '~/components/landing/LandingFooter';
import { PipelineDiagram } from '~/components/landing/PipelineDiagram';
import { RediscoveryGrid } from '~/components/landing/RediscoveryGrid';
import { TheoremBrowser } from '~/components/landing/TheoremBrowser';
import { WorkerMap } from '~/components/landing/WorkerMap';

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
            <a href="#how">How it works</a>
            <Link to="/browse">Browse corpus</Link>
            <Link to="/leaderboard">Contributors</Link>
            <Link to="/api-docs">API</Link>
            <Link to="/pricing">Pricing</Link>
            <span className="nav-sep" aria-hidden />
            <Link to="/signin" className="nav-secondary">
              Sign in
            </Link>
            <a href="#run" className="nav-cta text-white">
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

              <div className="hero-quote">
                <div className="hero-quote-text">
                  "Once, looking for a lost key under a lamppost, Nasrudin was asked why he searched
                  there. <em>Because the light is better here.</em>"
                </div>
                <div className="hero-quote-attr">
                  — a Sufi parable. We point the lamp where Lean can prove.
                </div>
              </div>

              <div className="hero-ctas">
                <a className="btn btn-primary" href="#run">
                  Run a worker node <span className="btn-arrow">→</span>
                </a>
                <Link className="btn btn-secondary" to="/browse">
                  Browse the verified corpus
                </Link>
              </div>

              <div className="hero-meta">
                <div className="hero-meta-item">
                  <div className="hero-meta-num">350,124</div>
                  <div className="hero-meta-label">Mathlib axioms</div>
                </div>
                <div className="hero-meta-item">
                  <div className="hero-meta-num">43</div>
                  <div className="hero-meta-label">Physics postulates</div>
                </div>
                <div className="hero-meta-item">
                  <div className="hero-meta-num">1,247</div>
                  <div className="hero-meta-label">Workers · live</div>
                </div>
                <div className="hero-meta-item">
                  <div className="hero-meta-num">3.2 M</div>
                  <div className="hero-meta-label">Theorems / minute</div>
                </div>
              </div>
            </div>

            <div>
              <div className="overline" style={{ marginBottom: 12 }}>
                Live · just verified
              </div>
              <HeroLiveTheorem />
              <div
                className="margin-note"
                style={{
                  marginTop: 24,
                  paddingLeft: 16,
                  borderLeft: '2px dashed var(--terracotta-300)',
                  maxWidth: 360,
                }}
              >
                Every proof is reproducible — download the .lean file and re-run{' '}
                <span style={{ fontFamily: 'var(--font-mono)', fontSize: 14 }}>lake build</span> on
                your own machine.
              </div>
            </div>
          </div>
        </div>
      </section>

      <section className="section" id="how">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 01 / 06</div>
            <div className="section-title-block">
              <span className="overline">The pipeline</span>
              <h2 className="section-title">
                Five stages, one rule:{' '}
                <em>nothing enters the corpus that Lean&nbsp;4 hasn't proved twice.</em>
              </h2>
              <p className="section-lede">
                Workers run the full Rust GA + Lean 4 prover locally and only upload theorems
                they've already verified. The central server then re-verifies every submission with
                its own Lean instance before accepting it. Double-verification, no trust.
              </p>
            </div>
          </div>
          <PipelineDiagram />
          <div className="margin-note" style={{ marginTop: 32, textAlign: 'center' }}>
            ~98% of candidates are rejected. The wise fool is patient.
          </div>
        </div>
      </section>

      <section className="section compact">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 02 / 06</div>
            <div className="section-title-block">
              <span className="overline">Inside one cycle</span>
              <h2 className="section-title">
                Watch the GA <em>arrive at Newton</em> — without being told.
              </h2>
              <p className="section-lede">
                Mutate. Crossover. Compose. Verify. Five generations from the Lagrangian seed to{' '}
                <i>F = ma</i>, all of it formal.
              </p>
            </div>
          </div>
          <GAViz />
        </div>
      </section>

      <section className="section" id="discoveries">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 03 / 06</div>
            <div className="section-title-block">
              <span className="overline">Featured rediscoveries</span>
              <h2 className="section-title">
                Physics that <em>found itself</em> — and physics still in the dark.
              </h2>
              <p className="section-lede">
                Some of these were rediscovered without supervision. Others are search targets we're
                patiently waiting for. Each carries the GA cycle it emerged from and a re-runnable
                Lean proof.
              </p>
            </div>
          </div>
          <RediscoveryGrid />
        </div>
      </section>

      <section className="section" id="network">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 04 / 06</div>
            <div className="section-title-block">
              <span className="overline">The network</span>
              <h2 className="section-title">
                A distributed prover, <em>built from home PCs and cloud nodes.</em>
              </h2>
              <p className="section-lede">
                Anyone can run a worker. Each generates and verifies theorems locally, then POSTs
                discoveries to the central server, which re-verifies before accepting. The server is
                the gatekeeper, not the oracle.
              </p>
            </div>
          </div>
          <WorkerMap />
        </div>
      </section>

      <section className="section" id="browse-teaser">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 05 / 06</div>
            <div className="section-title-block">
              <span className="overline">The corpus</span>
              <h2 className="section-title">
                Every theorem. Every proof. <em>Trust the math, not the server.</em>
              </h2>
              <p className="section-lede">
                Click any row to see its full Lean 4 proof. Download the .lean file and re-verify it
                on your own machine with{' '}
                <code
                  style={{
                    fontFamily: 'var(--font-mono)',
                    fontSize: 14,
                    padding: '2px 8px',
                    background: 'var(--paper-100)',
                    borderRadius: 4,
                  }}
                >
                  lake build
                </code>
                . The corpus is open, browsable, and reproducible by construction.
              </p>
            </div>
          </div>
          <TheoremBrowser />
        </div>
      </section>

      <section className="section" id="run">
        <div className="container-wide">
          <div className="section-head">
            <div className="section-num">§ 06 / 06</div>
            <div className="section-title-block">
              <span className="overline">Contribute compute</span>
              <h2 className="section-title">
                Run a worker. <em>Help physics rediscover itself.</em>
              </h2>
              <p className="section-lede">
                Three commands — install, register, run. Your machine starts mutating axioms in
                seconds. Every theorem your node verifies and the server accepts gets your pseudonym
                attached, forever.
              </p>
            </div>
          </div>
          <InstallNode />
        </div>
      </section>

      <LandingFooter />
    </div>
  );
}
