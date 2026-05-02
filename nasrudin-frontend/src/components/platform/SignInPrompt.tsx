import { Link } from '@tanstack/react-router';
import type { ReactNode } from 'react';
import { AppFooter } from './AppFooter';
import { AppHeader } from './AppHeader';

interface Props {
  active?: string;
  overline: string;
  title: string;
  description: ReactNode;
}

/// Logged-out placeholder for routes that require auth. Renders the
/// same chrome (header + footer) as the real page so navigation and
/// branding stay intact, plus a clear sign-in CTA explaining what the
/// user gets after signing in. Replaces the older `throw redirect` flow
/// that bounced unauthenticated visitors straight to /signin (which both
/// hid the page's purpose and surfaced a raw 401 when a route loader
/// touched a `/api/me/*` endpoint before the redirect could fire).
export function SignInPrompt({ active, overline, title, description }: Props) {
  return (
    <div className="app">
      {active === undefined ? <AppHeader /> : <AppHeader active={active} />}
      <div className="container-wide" style={{ maxWidth: 720 }}>
        <div className="page-head">
          <span className="overline">{overline}</span>
          <h1>{title}</h1>
          <p className="lede">{description}</p>
        </div>
        <div
          className="page-body"
          style={{
            padding: '48px 32px',
            textAlign: 'center',
            border: '1px dashed var(--paper-300)',
            borderRadius: 'var(--radius-lg)',
            background: 'var(--paper-50)',
          }}
        >
          <p style={{ color: 'var(--ink-700)', fontSize: 15, marginBottom: 20 }}>
            You'll need an account to use this page.
          </p>
          <div style={{ display: 'flex', gap: 12, justifyContent: 'center' }}>
            <Link to="/signin" className="btn btn-primary">
              Sign in
            </Link>
            <Link to="/browse" className="btn btn-ghost">
              Browse the corpus
            </Link>
          </div>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}
