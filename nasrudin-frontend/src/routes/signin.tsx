import { createFileRoute, Link } from '@tanstack/react-router';
import { AuthForm } from '~/components/auth/AuthForm';

export const Route = createFileRoute('/signin')({ component: SignInPage });

function SignInPage() {
  return (
    <div className="auth-page">
      <div className="auth-side">
        <div className="auth-side-pattern" />
        <Link to="/" className="auth-side-brand" style={{ textDecoration: 'none' }}>
          Nasrud
          <span
            style={{
              display: 'inline-block',
              width: 6,
              height: 6,
              borderRadius: '50%',
              background: 'var(--terracotta-500)',
              transform: 'translateY(-2px)',
              margin: '0 1px',
            }}
          />
          in
        </Link>
        <div>
          <div className="auth-side-quote">
            "Once, looking for a lost key under a lamppost, Nasrudin was asked why he searched
            there. <em>Because the light is better here.</em>"
          </div>
          <div className="auth-side-attr">— a Sufi parable</div>
        </div>
        <div className="auth-stat-row">
          <div className="auth-stat">
            <div className="num">247,118</div>
            <div className="lbl">Verified theorems</div>
          </div>
          <div className="auth-stat">
            <div className="num">1,247</div>
            <div className="lbl">Workers · live</div>
          </div>
          <div className="auth-stat">
            <div className="num">42</div>
            <div className="lbl">Countries</div>
          </div>
        </div>
      </div>
      <AuthForm />
    </div>
  );
}
