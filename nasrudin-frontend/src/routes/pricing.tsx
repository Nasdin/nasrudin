import { createFileRoute } from '@tanstack/react-router';
import { useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';

export const Route = createFileRoute('/pricing')({ component: PricingPage });

interface Tier {
  name: string;
  tagline: string;
  price: string;
  period: string;
  sub: string;
  cta: string;
  ctaClass: string;
  featured?: boolean;
  popular?: boolean;
  features: string[];
}

const TIERS: Tier[] = [
  {
    name: 'Free',
    tagline: 'For curious academics, students, and the merely intrigued.',
    price: '$0',
    period: 'forever',
    sub: 'no card required',
    cta: 'Sign up',
    ctaClass: 'btn-secondary',
    features: [
      'Browse all 247,118 verified theorems',
      'Read full Lean 4 proofs',
      'Download any .lean file & re-verify locally',
      'Save up to 50 theorems to your library',
      'Cite & share via permalinks',
      'Community discussion threads',
    ],
  },
  {
    name: 'Researcher',
    tagline: 'For working academics with active conjectures.',
    price: '$19',
    period: '/ month',
    sub: 'billed annually · $228/yr',
    cta: 'Start 14-day trial',
    ctaClass: 'btn-primary',
    featured: true,
    popular: true,
    features: [
      'Everything in Free',
      '10 targeted searches / month',
      'Point the GA at your own conjecture',
      'API access · 10K requests / day',
      'Unlimited library, folders & private notes',
      'Email digest of new theorems in your domains',
      'Priority re-verification queue',
    ],
  },
  {
    name: 'Lab',
    tagline: 'For research groups, departments, and small institutes.',
    price: '$249',
    period: '/ month',
    sub: 'up to 10 seats · billed annually',
    cta: 'Talk to us',
    ctaClass: 'btn-secondary',
    features: [
      'Everything in Researcher, for 10 seats',
      '100 targeted searches / month (pooled)',
      'API · 250K requests / day',
      'Shared lab library & citation graphs',
      'Bulk .lean exports for your codebase',
      'SSO via institution',
      'Quarterly office hours with the team',
    ],
  },
  {
    name: 'Enterprise',
    tagline: 'For institutions running their own Nasrudin nodes.',
    price: 'Custom',
    period: '',
    sub: 'annual · invoiced',
    cta: 'Contact sales',
    ctaClass: 'btn-secondary',
    features: [
      'Everything in Lab, unlimited seats',
      'Dedicated targeted-search compute pool',
      'On-prem worker cluster deployment',
      'Private corpus extension (your own axioms)',
      'Service-level agreement · 99.9%',
      'Audit logs & compliance reporting',
      'Direct line to engineering',
    ],
  },
];

const FAQ: Array<[string, string]> = [
  [
    'Is the underlying corpus really free?',
    'Yes. All 247,118 verified theorems are browseable, downloadable as .lean files, and re-verifiable on your own machine without a paid plan.',
  ],
  [
    'What is a "targeted search"?',
    'You provide a conjecture in Lean syntax (or natural-language we transcribe). We dedicate a slice of the GA cluster to evolve toward it for up to 24 hours.',
  ],
  [
    'Can I cancel anytime?',
    'Yes. Researcher and Lab tiers cancel at the end of the current billing period.',
  ],
  [
    'Are workers paid?',
    'No. Worker contributions are volunteer compute. Workers earn status (leaderboard rank, attribution on every theorem they verify) but no money.',
  ],
  [
    'Educational discount?',
    'Researcher tier is free for verified students. Email proof from a .edu / .ac.* address.',
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
            The corpus is open by principle. What we charge for is compute — the slices of GA
            cluster you point at your own conjectures, and the API that lets you build on top of
            Nasrudin.
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
                <span className="tier-price-num">{t.price}</span>
                <span className="tier-price-period">{t.period}</span>
              </div>
              <div className="tier-price-sub">{t.sub}</div>
              <button type="button" className={`btn ${t.ctaClass}`}>
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
