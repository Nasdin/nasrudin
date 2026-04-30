import { createFileRoute } from '@tanstack/react-router';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { API_BASE } from '~/lib/api';

export const Route = createFileRoute('/sponsor')({
  component: SponsorPage,
  validateSearch: (search: Record<string, unknown>): { thanks?: string } =>
    typeof search.thanks === 'string' ? { thanks: search.thanks } : {},
});

interface Tier {
  name: string;
  amount: string;
  description: string;
  priceKey: 'sponsor_5' | 'sponsor_25' | 'sponsor_100' | 'sponsor_open';
  /// Recurring subscription tile copy. The pay-what-you-want tile uses
  /// "Donate" because it's a one-time charge with no renewal.
  cta: 'monthly' | 'one_time';
}

const TIERS: Tier[] = [
  {
    name: 'Coffee',
    amount: '$5 / month',
    description:
      'Buys ~one hour of Lean4 verification time. Keeps the lights on and the workers fed.',
    priceKey: 'sponsor_5',
    cta: 'monthly',
  },
  {
    name: 'Pizza',
    amount: '$25 / month',
    description:
      'Underwrites a slice of the central re-verification cluster. The corpus stays open because of you.',
    priceKey: 'sponsor_25',
    cta: 'monthly',
  },
  {
    name: 'Cluster Hour',
    amount: '$100 / month',
    description:
      'Sponsors meaningful targeted-search compute and lets us point cycles at open conjectures with no paying buyer attached.',
    priceKey: 'sponsor_100',
    cta: 'monthly',
  },
  {
    name: 'Open',
    amount: 'Custom amount',
    description:
      'Pay what you can. One-time donation, any amount you choose. Helpful when you want to chip in without committing to a recurring subscription.',
    priceKey: 'sponsor_open',
    cta: 'one_time',
  },
];

const ONE_TIME_LINK =
  (import.meta.env.VITE_STRIPE_SPONSOR_PAYMENT_LINK as string | undefined) ?? '';

async function startSponsor(priceKey: Tier['priceKey']) {
  const res = await fetch(`${API_BASE}/api/billing/checkout`, {
    method: 'POST',
    credentials: 'include',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ price_key: priceKey }),
  });
  if (res.status === 401) {
    window.location.href = `/signin?next=${encodeURIComponent('/sponsor')}`;
    return;
  }
  if (!res.ok) {
    alert('Sponsor checkout unavailable right now. Try again or use the one-time link below.');
    return;
  }
  const { url } = (await res.json()) as { url: string };
  window.location.href = url;
}

function SponsorPage() {
  const { thanks } = Route.useSearch();
  return (
    <div className="app">
      <AppHeader />
      <div className="container-wide" style={{ paddingTop: 64, paddingBottom: 96 }}>
        {thanks && (
          <div
            style={{
              padding: 16,
              marginBottom: 32,
              border: '1px solid var(--olive-700)',
              background: 'var(--olive-100)',
              borderRadius: 8,
              color: 'var(--ink-900)',
            }}
          >
            Thank you. Your sponsorship keeps the network running.
          </div>
        )}
        <span className="overline">Sponsor</span>
        <h1 style={{ marginTop: 12 }}>
          Keep the corpus <em>free</em>.
        </h1>
        <p className="lede" style={{ maxWidth: 720 }}>
          Nasrudin's verified-theorem corpus is built by volunteer worker compute and stays free
          forever. Sponsorships fund what volunteers can't carry: central Lean4 re-verification,
          API hosting, the embedding index, and the engineering time to keep all of it running.
        </p>
        <p className="lede" style={{ maxWidth: 720, color: 'var(--ink-500)', fontSize: 16 }}>
          Sponsorship is a donation, not a subscription tier — you don't get extra targeted
          searches or higher API quotas. You get the satisfaction of knowing this stays open. If
          you want service-tier access to commission targeted compute, see{' '}
          <a href="/pricing">Pricing</a>.
        </p>

        <div
          style={{
            display: 'grid',
            gridTemplateColumns: 'repeat(auto-fit, minmax(280px, 1fr))',
            gap: 24,
            marginTop: 48,
          }}
        >
          {TIERS.map((t) => (
            <div
              key={t.priceKey}
              style={{
                padding: 28,
                border: '1px solid var(--paper-200)',
                borderRadius: 12,
                background: 'var(--bg-raised)',
                display: 'flex',
                flexDirection: 'column',
                gap: 12,
              }}
            >
              <div
                style={{
                  fontFamily: 'var(--font-serif)',
                  fontSize: 22,
                  color: 'var(--ink-900)',
                }}
              >
                {t.name}
              </div>
              <div
                style={{
                  fontSize: 28,
                  fontWeight: 500,
                  color: 'var(--ink-900)',
                }}
              >
                {t.amount}
              </div>
              <p style={{ color: 'var(--ink-500)', fontSize: 14, lineHeight: 1.5, flex: 1 }}>
                {t.description}
              </p>
              <button
                type="button"
                className="btn btn-primary"
                onClick={() => startSponsor(t.priceKey)}
              >
                {t.cta === 'monthly' ? 'Sponsor monthly' : 'Donate'}
              </button>
            </div>
          ))}
        </div>

        {ONE_TIME_LINK && (
          <div
            style={{
              marginTop: 56,
              padding: 24,
              borderTop: '1px solid var(--paper-200)',
              textAlign: 'center',
            }}
          >
            <p style={{ color: 'var(--ink-700)', fontSize: 16, marginBottom: 12 }}>
              Prefer a one-time gift?
            </p>
            <a
              href={ONE_TIME_LINK}
              className="btn btn-secondary"
              target="_blank"
              rel="noopener noreferrer"
            >
              Name your amount →
            </a>
            <p style={{ color: 'var(--ink-500)', fontSize: 13, marginTop: 12 }}>
              Hosted by Stripe · choose any amount from $5
            </p>
          </div>
        )}

        <section style={{ marginTop: 80 }}>
          <span className="overline">Where the money goes</span>
          <h2
            style={{
              fontFamily: 'var(--font-serif)',
              fontSize: 32,
              fontWeight: 400,
              margin: '12px 0 24px',
              color: 'var(--ink-900)',
            }}
          >
            Operating costs, in order.
          </h2>
          <ul style={{ color: 'var(--ink-700)', lineHeight: 1.7, fontSize: 15 }}>
            <li>
              <strong>Central Lean4 re-verification</strong> — every worker submission is
              independently re-checked on our side before joining the global corpus.
            </li>
            <li>
              <strong>Embedding index hosting</strong> — semantic search over the whole corpus
              runs on hardware that costs money to keep online.
            </li>
            <li>
              <strong>API and frontend</strong> — Postgres, RocksDB, the web UI, KaTeX rendering.
            </li>
            <li>
              <strong>Engineering time</strong> — keeping the GA, the prover bridge, and the
              ingest pipeline alive and improving.
            </li>
          </ul>
        </section>
      </div>
      <AppFooter />
    </div>
  );
}
