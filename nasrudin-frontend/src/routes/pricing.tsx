import { createFileRoute } from '@tanstack/react-router';
import { useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';

export const Route = createFileRoute('/pricing')({ component: PricingPage });

interface Tier {
  name: string;
  tagline: string;
  monthlyPrice: string;
  annualPrice: string;
  period: string;
  monthlySub: string;
  annualSub: string;
  cta: string;
  ctaClass: string;
  /** Phase 1 sells Researcher self-serve. Other tiers route to the
   *  sales-contact flow until org subscriptions ship. */
  priceKey: 'researcher_monthly' | 'researcher_annual' | null;
  featured?: boolean;
  popular?: boolean;
  features: string[];
}

const TIERS: Tier[] = [
  {
    name: 'Free',
    tagline: 'For citing, browsing, and re-verifying. No card.',
    monthlyPrice: '$0',
    annualPrice: '$0',
    period: 'forever',
    monthlySub: 'no card required',
    annualSub: 'no card required',
    cta: 'Sign up',
    ctaClass: 'btn-secondary',
    priceKey: null,
    features: [
      'Browse the full verified theorem corpus',
      'Read full Lean 4 proofs',
      'Download any .lean file & re-verify locally',
      'Save up to 50 theorems',
      'Cite & share via permalinks',
      '1,000 API requests / day',
    ],
  },
  {
    name: 'Researcher',
    tagline: 'For builders pointing compute at hard problems.',
    monthlyPrice: '$19',
    annualPrice: '$15.20',
    period: '/ month',
    monthlySub: 'billed monthly',
    annualSub: 'billed annually · $182.40/yr (−20%)',
    cta: 'Start subscription',
    ctaClass: 'btn-primary',
    featured: true,
    popular: true,
    priceKey: 'researcher_monthly',
    features: [
      'Everything in Free',
      '10 targeted searches / month',
      'Point the GA at your own conjecture',
      '10,000 API requests / day',
      'Unlimited library, folders, private notes',
      'Email digest of new theorems in your domains',
    ],
  },
  {
    name: 'Team',
    tagline: 'For research groups: pooled searches, shared library.',
    monthlyPrice: '$57',
    annualPrice: '$45.60',
    period: '/ month',
    monthlySub: '3 seats included · +$19/seat · billed monthly',
    annualSub: '3 seats included · +$15.20/seat · billed annually',
    cta: 'Talk to us',
    ctaClass: 'btn-secondary',
    priceKey: null,
    features: [
      'Everything in Researcher, per seat',
      '50 targeted searches / month (pooled)',
      '50,000 API requests / day (pooled)',
      'Shared library & citation graphs',
      'Google / Microsoft sign-in',
      'Bulk .lean exports',
    ],
  },
  {
    name: 'Institution',
    tagline: 'For departments and institutes with compliance needs.',
    monthlyPrice: '$990',
    annualPrice: '$792',
    period: '/ month',
    monthlySub: '10 seats included · +$99/seat · billed monthly',
    annualSub: '10 seats included · +$79.20/seat · billed annually',
    cta: 'Contact sales',
    ctaClass: 'btn-secondary',
    priceKey: null,
    features: [
      'Everything in Team, per seat',
      '200 targeted searches / month (pooled)',
      '250,000 API requests / day (pooled)',
      'SAML SSO',
      'Audit logs & compliance reporting',
      'Dedicated targeted-search compute pool',
      'Quarterly office hours',
    ],
  },
  {
    name: 'Enterprise',
    tagline: 'For institutions running their own Nasrudin nodes.',
    monthlyPrice: 'Custom',
    annualPrice: 'Custom',
    period: '',
    monthlySub: 'annual · invoiced',
    annualSub: 'annual · invoiced',
    cta: 'Contact sales',
    ctaClass: 'btn-secondary',
    priceKey: null,
    features: [
      'Everything in Institution, unlimited seats',
      'On-prem worker cluster deployment',
      'Private corpus extension (your own axioms)',
      'SLA · 99.9%',
      'Direct line to engineering',
    ],
  },
];

const FAQ: Array<[string, string]> = [
  [
    'Is the underlying corpus really free?',
    'Yes. Every verified theorem is browseable, downloadable as a .lean file, and re-verifiable on your own machine without a paid plan. The corpus is built by volunteer worker compute and stays free by design.',
  ],
  [
    'What is a "targeted search"?',
    'You provide a conjecture in Lean syntax (or natural language we transcribe). We dedicate a slice of the GA cluster to evolve toward it for up to 24 hours. Paid tiers buy targeted compute aimed at *your* conjecture — the open corpus is never gated.',
  ],
  [
    'Can I cancel anytime?',
    'Yes. Self-serve cancel from the billing portal — your plan stays active through the end of the current period.',
  ],
  [
    'Are workers paid?',
    "No cash. Workers earn (1) attribution on every theorem they verify, (2) leaderboard rank, and (3) — coming soon — a free Researcher tier when contributing ≥10 hours of verification time per month. Compute donated by workers builds the open corpus; paid tiers buy targeted GA slices pointed at the buyer's own conjecture.",
  ],
  [
    'Are you a tool for academics specifically?',
    'No — Nasrudin is for anyone pointing compute at hard problems. Independent researchers, industry R&D, quant teams, and academics with budget all use it the same way. Verified academic email gets 50% off Researcher.',
  ],
];

function Check() {
  return (
    <svg
      width="14"
      height="14"
      viewBox="0 0 24 24"
      fill="none"
      stroke="currentColor"
      strokeWidth="2.2"
      strokeLinecap="round"
      strokeLinejoin="round"
      aria-hidden="true"
    >
      <polyline points="20 6 9 17 4 12" />
    </svg>
  );
}

async function startCheckout(tier: Tier, annual: boolean) {
  if (!tier.priceKey) return;
  const key = annual
    ? (tier.priceKey.replace('_monthly', '_annual') as 'researcher_annual')
    : tier.priceKey;
  const res = await fetch('/api/billing/checkout', {
    method: 'POST',
    credentials: 'include',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ price_key: key }),
  });
  if (res.status === 401) {
    window.location.href = `/signin?next=${encodeURIComponent('/pricing')}`;
    return;
  }
  if (!res.ok) {
    alert('Checkout unavailable right now. Try again or contact support.');
    return;
  }
  const { url } = (await res.json()) as { url: string };
  window.location.href = url;
}

function PricingPage() {
  const [annual, setAnnual] = useState(true);
  return (
    <div className="app">
      <AppHeader active="pricing" />
      <div className="container-wide">
        <div className="pricing-hero">
          <span className="overline">Pricing</span>
          <h1 style={{ marginTop: 12 }}>
            Free to <em>read.</em> Paid to <em>aim.</em>
          </h1>
          <p className="lede">
            The corpus is open by principle — built by volunteer compute and free forever. What we
            charge for is targeted compute: the slices of GA cluster you point at your own
            conjecture, plus the API that lets you build on top of Nasrudin.
          </p>
          <div
            style={{
              display: 'inline-flex',
              marginTop: 32,
              padding: 4,
              background: 'var(--paper-100)',
              borderRadius: 999,
              border: '1px solid var(--paper-200)',
            }}
          >
            <button
              type="button"
              onClick={() => setAnnual(false)}
              style={{
                padding: '6px 16px',
                fontSize: 13,
                border: 'none',
                borderRadius: 999,
                background: !annual ? 'var(--bg-raised)' : 'transparent',
                color: 'var(--ink-900)',
                cursor: 'pointer',
                boxShadow: !annual ? 'var(--shadow-sm)' : 'none',
                fontFamily: 'var(--font-sans)',
                fontWeight: 500,
              }}
            >
              Monthly
            </button>
            <button
              type="button"
              onClick={() => setAnnual(true)}
              style={{
                padding: '6px 16px',
                fontSize: 13,
                border: 'none',
                borderRadius: 999,
                background: annual ? 'var(--bg-raised)' : 'transparent',
                color: 'var(--ink-900)',
                cursor: 'pointer',
                boxShadow: annual ? 'var(--shadow-sm)' : 'none',
                fontFamily: 'var(--font-sans)',
                fontWeight: 500,
              }}
            >
              Annual{' '}
              <span style={{ color: 'var(--olive-700)', fontSize: 11, marginLeft: 4 }}>−20%</span>
            </button>
          </div>
        </div>

        <div className="tier-grid">
          {TIERS.map((t) => (
            <div key={t.name} className={`tier ${t.featured ? 'featured' : ''}`}>
              {t.popular && <span className="tier-popular">Most popular</span>}
              <div className="tier-name">{t.name}</div>
              <div className="tier-tagline">{t.tagline}</div>
              <div className="tier-price">
                <span className="tier-price-num">{annual ? t.annualPrice : t.monthlyPrice}</span>
                <span className="tier-price-period">{t.period}</span>
              </div>
              <div className="tier-price-sub">{annual ? t.annualSub : t.monthlySub}</div>
              <button
                type="button"
                className={`btn ${t.ctaClass}`}
                onClick={() => startCheckout(t, annual)}
              >
                {t.cta}
              </button>
              <ul className="tier-features">
                {t.features.map((f) => (
                  <li key={f}>
                    <Check />
                    <span>{f}</span>
                  </li>
                ))}
              </ul>
            </div>
          ))}
        </div>

        <section
          className="section compact"
          style={{ borderTop: '1px solid var(--paper-200)', padding: '64px 0' }}
        >
          <span className="overline">Questions</span>
          <h2
            style={{
              fontFamily: 'var(--font-serif)',
              fontSize: 36,
              fontWeight: 400,
              letterSpacing: '-0.025em',
              margin: '12px 0 8px',
              color: 'var(--ink-900)',
            }}
          >
            The usual ones, answered straight.
          </h2>
          <div className="faq-grid">
            {FAQ.map(([q, a]) => (
              <div className="faq-item" key={q}>
                <h4>{q}</h4>
                <p>{a}</p>
              </div>
            ))}
          </div>
        </section>
      </div>
      <AppFooter />
    </div>
  );
}
