import { createFileRoute, Link } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import { recentTheoremsOptions, useLandingStats, useRecentTheorems } from '~/lib/queries';
import { useDiscoveryFeed } from '~/lib/sse';
import type { Theorem } from '~/lib/types';

export const Route = createFileRoute('/discoveries')({
  loader: async ({ context }) => {
    await context.queryClient.ensureQueryData(recentTheoremsOptions(20));
  },
  component: DiscoveriesPage,
});

interface Rediscovery {
  name: string;
  stmt: string;
  domain: string;
  gen: number | null;
  axioms: number | null;
  ga_cycle: number | null;
  found_on: string | null;
  desc: string;
  status: 'rediscovered' | 'pending';
}

const REDISCOVERIES: Rediscovery[] = [
  {
    name: "Einstein's mass–energy equivalence",
    stmt: 'E = m \\cdot c^2',
    domain: 'SpecialRelativity',
    gen: 12,
    axioms: 3,
    ga_cycle: 4_211,
    found_on: '2026-02-14',
    desc: 'The GA started from Lorentz invariance + the action principle and proposed the rest-energy term as a degenerate limit of the relativistic Hamiltonian. Verified in 8.4s of Lean.',
    status: 'rediscovered',
  },
  {
    name: "Newton's second law",
    stmt: 'F = m \\cdot a',
    domain: 'ClassicalMechanics',
    gen: 6,
    axioms: 4,
    ga_cycle: 1_044,
    found_on: '2025-11-02',
    desc: 'Emerged from a Lagrangian seed and Euler–Lagrange composition. Five generations later F=ma surfaced directly, side-by-side with Lagrange\'s equation.',
    status: 'rediscovered',
  },
  {
    name: "Maxwell's free-space wave equation",
    stmt: '\\nabla^2 E = \\frac{1}{c^2} \\frac{\\partial^2 E}{\\partial t^2}',
    domain: 'Electromagnetism',
    gen: 18,
    axioms: 5,
    ga_cycle: 8_902,
    found_on: '2026-03-21',
    desc: 'Rediscovered after composing Faraday + Ampère. Light\'s speed fell out of vacuum permittivity & permeability — no fitting.',
    status: 'rediscovered',
  },
  {
    name: 'Heisenberg uncertainty',
    stmt: '\\sigma_x^2 \\cdot \\sigma_p^2 \\geq \\hbar^2 / 4',
    domain: 'QuantumMechanics',
    gen: 14,
    axioms: 5,
    ga_cycle: 12_711,
    found_on: '2026-04-10',
    desc: 'Found from the canonical commutation relation + Cauchy–Schwarz on Hilbert-space operators. Several near-misses preceded the exact bound.',
    status: 'rediscovered',
  },
  {
    name: "Bell's inequality (locality bound)",
    stmt: '|E(a,b) - E(a,c)| \\leq 1 + E(b,c)',
    domain: 'QuantumMechanics',
    gen: null,
    axioms: null,
    ga_cycle: null,
    found_on: null,
    desc: 'Search target. The GA has explored 2.1M candidate inequalities under hidden-variable axioms and is currently within four generations of the canonical form.',
    status: 'pending',
  },
  {
    name: "Noether's theorem (continuous symmetry)",
    stmt: '\\partial L / \\partial t = 0 \\Rightarrow \\exists \\text{ conserved } Q',
    domain: 'ClassicalMechanics',
    gen: null,
    axioms: null,
    ga_cycle: null,
    found_on: null,
    desc: 'Search target. The GA has the Lagrangian, action principle, and a calculus of variations module. Remaining gap: a formal axiom for one-parameter Lie groups.',
    status: 'pending',
  },
];

function timeAgo(iso: string | null): string {
  if (!iso) return '—';
  const ms = Date.now() - new Date(iso).getTime();
  if (ms < 60_000) return `${Math.max(1, Math.round(ms / 1000))}s ago`;
  if (ms < 3_600_000) return `${Math.round(ms / 60_000)}m ago`;
  if (ms < 86_400_000) return `${Math.round(ms / 3_600_000)}h ago`;
  return `${Math.round(ms / 86_400_000)}d ago`;
}

function RecentRow({ thm }: { thm: Theorem }) {
  const id = bytesToHex(thm.id);
  return (
    <Link to="/theorem/$id" params={{ id }} className="disc-recent-row">
      <div>
        <div className="disc-recent-stmt">
          <MathExpr source={thm.latex ?? thm.canonical_statement} />
        </div>
        <div className="disc-recent-meta">
          <strong>thm:{id.slice(0, 8)}</strong>
          <span>· {thm.domain}</span>
          {thm.generation != null && <span>· gen {thm.generation}</span>}
          {thm.depth != null && <span>· depth {thm.depth}</span>}
        </div>
      </div>
      <div className="disc-recent-side">
        <span className="badge badge-verified">✓ verified</span>
        <div className="disc-recent-time">{timeAgo(thm.verified_at)}</div>
      </div>
    </Link>
  );
}

function DiscoveriesPage() {
  // Live invalidation: any new verified theorem refreshes the recent
  // list. Same SSE stream the browse page uses.
  useDiscoveryFeed();
  const { data } = useRecentTheorems(20);
  const { data: stats } = useLandingStats();
  const recent = data?.theorems ?? [];

  return (
    <div className="app">
      <AppHeader active="discoveries" />

      <section className="disc-hero">
        <div className="container-wide">
          <span className="overline">Featured rediscoveries</span>
          <h1>
            Physics that <em>found itself.</em>
          </h1>
          <p className="lede">
            We pointed a genetic algorithm at a handful of axioms and let it run. These
            are the laws it rediscovered — without supervision, with formal proofs in
            Lean&nbsp;4. And these are the ones we&rsquo;re patiently waiting on.
          </p>
        </div>
      </section>

      <div className="container-wide page-body">
        <div className="disc-section-head">
          <div>
            <span className="overline disc-overline-live">Live · just verified</span>
            <h2>Recently discovered theorems</h2>
            <p className="disc-section-sub">
              Every result the GA produced in the last few hours. Most aren&rsquo;t
              Nobel-grade — they&rsquo;re the steady churn of the corpus growing.
            </p>
          </div>
          <Link to="/browse" className="btn btn-ghost">
            Browse all
            {stats?.verified_theorems != null
              ? ` ${stats.verified_theorems.toLocaleString()}`
              : ''}{' '}
            →
          </Link>
        </div>

        <div className="disc-recent-list">
          {recent.length === 0 ? (
            <div className="disc-recent-empty">Waiting for the next verification…</div>
          ) : (
            recent.slice(0, 12).map((thm) => (
              <RecentRow key={bytesToHex(thm.id)} thm={thm} />
            ))
          )}
        </div>

        <div className="disc-marquee">
          <div>
            <span className="overline">Cycle 4,211 · February 2026</span>
            <h2>
              The GA arrived at <em>E = m·c²</em> on its own.
            </h2>
            <p>{REDISCOVERIES[0]?.desc}</p>
            <div className="disc-marquee-actions">
              <Link to="/browse" className="btn btn-primary">
                Read the proof →
              </Link>
              <a className="btn btn-ghost-light">Download .lean</a>
            </div>
          </div>
          <div className="disc-marquee-stmt">
            <MathExpr source="E = m \cdot c^2" />
            <span className="disc-marquee-sub">verified in 8.4s · cycle 4,211</span>
          </div>
        </div>

        <div className="disc-section-head disc-section-head-second">
          <div>
            <h2>Marquee rediscoveries</h2>
            <p className="disc-section-sub">
              Hand-picked moments where the GA arrived at named, canonical results.
              The pending cards are the ones we&rsquo;re still searching for.
            </p>
          </div>
        </div>
        <div className="disc-grid">
          {REDISCOVERIES.map((r) => (
            <div
              key={r.name}
              className={`disc-card ${r.status === 'pending' ? 'is-pending' : ''}`}
            >
              <span className="disc-gen-tag">
                {r.status === 'rediscovered'
                  ? `gen ${r.gen} · cycle ${r.ga_cycle?.toLocaleString()}`
                  : 'search target'}
              </span>
              <h3>{r.name}</h3>
              <div className="disc-card-stmt">
                <MathExpr source={r.stmt} />
              </div>
              <p className="disc-card-desc">{r.desc}</p>
              <div className="disc-card-meta">
                <span>
                  <strong>{r.domain}</strong>
                </span>
                {r.found_on && <span>found {r.found_on}</span>}
                {r.axioms != null && <span>{r.axioms} axioms</span>}
              </div>
              {r.status === 'pending' && (
                <div className="disc-card-pending">— still searching —</div>
              )}
            </div>
          ))}
        </div>
      </div>

      <AppFooter />
    </div>
  );
}
