import { createFileRoute, Link } from '@tanstack/react-router';
import { useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';

export const Route = createFileRoute('/api-docs')({ component: ApiDocsPage });

interface CodeTab {
  lang: string;
  code: React.ReactNode;
}

function Tabs({ tabs }: { tabs: CodeTab[] }) {
  const [active, setActive] = useState(0);
  return (
    <div>
      <div className="code-tabs">
        {tabs.map((t, i) => (
          <button
            key={t.lang}
            type="button"
            className={`code-tab ${active === i ? 'active' : ''}`}
            onClick={() => setActive(i)}
          >
            {t.lang}
          </button>
        ))}
      </div>
      <pre className="code-block">{tabs[active]?.code}</pre>
    </div>
  );
}

function ApiDocsPage() {
  return (
    <div className="app">
      <AppHeader active="api" />
      <div className="container-wide">
        <div className="api-hero">
          <span className="overline">For builders</span>
          <h1
            style={{
              fontFamily: 'var(--font-serif)',
              fontSize: 'clamp(28px, 7vw, 48px)',
              fontWeight: 400,
              letterSpacing: '-0.025em',
              margin: '12px 0 12px',
            }}
          >
            Build on the corpus.
          </h1>
          <p className="lede" style={{ margin: '0 auto' }}>
            A REST + GraphQL API over every verified theorem, its proof, lineage, and downstream
            uses. Free for individual academics, metered for labs and enterprise.
          </p>
        </div>
        <div className="api-grid">
          <aside className="api-toc">
            <h6>Endpoints</h6>
            <ul>
              <li>
                <a href="#auth" className="active">
                  Authentication
                </a>
              </li>
              <li>
                <a href="#get-thm">GET /v1/theorems/:id</a>
              </li>
              <li>
                <a href="#search">GET /v1/search</a>
              </li>
              <li>
                <a href="#stream">GET /v1/stream</a>
              </li>
              <li>
                <a href="#limits">Rate limits</a>
              </li>
            </ul>
            <div
              style={{
                marginTop: 32,
                padding: 16,
                background: 'var(--paper-100)',
                borderRadius: 10,
                fontSize: 12,
                color: 'var(--ink-700)',
              }}
            >
              <strong
                style={{
                  color: 'var(--ink-900)',
                  fontFamily: 'var(--font-serif)',
                  fontSize: 14,
                  display: 'block',
                  marginBottom: 6,
                }}
              >
                Free tier
              </strong>
              10K req/day. No card. Higher limits on <Link to="/pricing">Researcher+</Link>.
            </div>
          </aside>
          <div>
            <section id="auth" style={{ marginBottom: 48 }}>
              <h3 style={{ fontFamily: 'var(--font-serif)', fontSize: 24, marginBottom: 12 }}>
                Authentication
              </h3>
              <p
                style={{
                  fontSize: 14,
                  color: 'var(--ink-700)',
                  marginBottom: 16,
                  lineHeight: 1.55,
                }}
              >
                Pass your API key as a Bearer token. Generate keys from your{' '}
                <Link to="/api-keys">API keys page</Link>. Never embed keys client-side.
              </p>
              <pre className="code-block">
                <span className="kw">curl</span> https://api.nasrudin.org/v1/theorems/9f3a2c8e \
                {'\n'} -H <span className="str">"Authorization: Bearer nsk_live_a98c…"</span>
              </pre>
            </section>
            <section className="endpoint" id="get-thm">
              <div className="endpoint-head">
                <span className="method get">GET</span>
                <span className="endpoint-path">/v1/theorems/:id</span>
                <span className="endpoint-tier">free</span>
              </div>
              <h3>Fetch a theorem</h3>
              <p className="desc">
                Returns the full theorem record: statement (Lean & MathML), proof, provenance,
                lineage IDs, and downstream theorem IDs.
              </p>
              <Tabs
                tabs={[
                  {
                    lang: 'curl',
                    code: (
                      <>
                        <span className="kw">curl</span> https://api.nasrudin.org/v1/theorems/
                        <span className="str">9f3a2c8e</span> \{'\n'} -H{' '}
                        <span className="str">"Authorization: Bearer $NSR_KEY"</span>
                      </>
                    ),
                  },
                  {
                    lang: 'python',
                    code: (
                      <>
                        <span className="kw">import</span> nasrudin{'\n'}
                        {'\n'}thm = nasrudin.<span className="nm">theorems</span>.get(
                        <span className="str">"9f3a2c8e"</span>){'\n'}
                        <span className="kw">print</span>(thm.statement_lean)
                      </>
                    ),
                  },
                  {
                    lang: 'node',
                    code: (
                      <>
                        <span className="kw">import</span> Nasrudin <span className="kw">from</span>{' '}
                        <span className="str">"@nasrudin/sdk"</span>;{'\n'}
                        <span className="kw">const</span> n = <span className="kw">new</span>{' '}
                        Nasrudin(process.env.NSR_KEY);{'\n'}
                        <span className="kw">const</span> thm = <span className="kw">await</span>{' '}
                        n.theorems.get(<span className="str">"9f3a2c8e"</span>);
                      </>
                    ),
                  },
                ]}
              />
            </section>
            <section className="endpoint" id="search">
              <div className="endpoint-head">
                <span className="method get">GET</span>
                <span className="endpoint-path">/v1/search?q=…&domain=…</span>
                <span className="endpoint-tier">free</span>
              </div>
              <h3>Search the corpus</h3>
              <p className="desc">
                Full-text + structural search across statements, names, and Lean tactics.
              </p>
              <pre className="code-block">
                <span className="kw">curl</span>{' '}
                <span className="str">
                  "https://api.nasrudin.org/v1/search?q=commutator&domain=quantum&limit=20"
                </span>{' '}
                \{'\n'} -H <span className="str">"Authorization: Bearer $NSR_KEY"</span>
              </pre>
            </section>
            <section className="endpoint" id="stream">
              <div className="endpoint-head">
                <span className="method get">GET</span>
                <span className="endpoint-path">/v1/stream</span>
                <span className="endpoint-tier">researcher+</span>
              </div>
              <h3>Live stream of new theorems</h3>
              <p className="desc">
                Server-sent events. Subscribe with optional domain filters and receive each newly
                verified theorem within ~2s of server acceptance.
              </p>
              <pre className="code-block">
                <span className="kw">const</span> es = <span className="kw">new</span> EventSource(
                <span className="str">"https://api.nasrudin.org/v1/stream?domain=quantum"</span>);
                {'\n'}es.onmessage = (e) =&gt; <span className="kw">console</span>.log(
                <span className="kw">JSON</span>.parse(e.data));
              </pre>
            </section>
            <section className="endpoint" id="limits">
              <div className="endpoint-head">
                <span className="method get">·</span>
                <span className="endpoint-path">Rate limits</span>
              </div>
              <table
                style={{
                  width: '100%',
                  borderCollapse: 'separate',
                  borderSpacing: 0,
                  fontSize: 13,
                }}
              >
                <thead>
                  <tr>
                    <th
                      style={{
                        textAlign: 'left',
                        padding: '10px 12px',
                        borderBottom: '1px solid var(--paper-200)',
                      }}
                    >
                      Tier
                    </th>
                    <th
                      style={{
                        textAlign: 'right',
                        padding: '10px 12px',
                        borderBottom: '1px solid var(--paper-200)',
                      }}
                    >
                      Reads / day
                    </th>
                    <th
                      style={{
                        textAlign: 'right',
                        padding: '10px 12px',
                        borderBottom: '1px solid var(--paper-200)',
                      }}
                    >
                      Stream
                    </th>
                  </tr>
                </thead>
                <tbody>
                  <tr>
                    <td style={{ padding: '12px' }}>Free</td>
                    <td
                      style={{
                        padding: '12px',
                        textAlign: 'right',
                        fontFamily: 'var(--font-mono)',
                      }}
                    >
                      500
                    </td>
                    <td style={{ padding: '12px', textAlign: 'right' }}>—</td>
                  </tr>
                  <tr>
                    <td style={{ padding: '12px' }}>Researcher</td>
                    <td
                      style={{
                        padding: '12px',
                        textAlign: 'right',
                        fontFamily: 'var(--font-mono)',
                      }}
                    >
                      10,000 / day
                    </td>
                    <td style={{ padding: '12px', textAlign: 'right' }}>✓</td>
                  </tr>
                  <tr>
                    <td style={{ padding: '12px' }}>Lab</td>
                    <td
                      style={{
                        padding: '12px',
                        textAlign: 'right',
                        fontFamily: 'var(--font-mono)',
                      }}
                    >
                      250,000 / day
                    </td>
                    <td style={{ padding: '12px', textAlign: 'right' }}>✓</td>
                  </tr>
                  <tr>
                    <td style={{ padding: '12px' }}>Enterprise</td>
                    <td
                      style={{
                        padding: '12px',
                        textAlign: 'right',
                        fontFamily: 'var(--font-mono)',
                      }}
                    >
                      custom
                    </td>
                    <td style={{ padding: '12px', textAlign: 'right' }}>✓</td>
                  </tr>
                </tbody>
              </table>
            </section>
          </div>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}
