import { useNavigate } from '@tanstack/react-router';
import { type FormEvent, useState } from 'react';
import { isApiError } from '~/lib/api';
import { useLogin, useRegister } from '~/lib/queries';

export function AuthForm() {
  const [tab, setTab] = useState<'signin' | 'signup'>('signin');
  const [email, setEmail] = useState('');
  const [password, setPassword] = useState('');
  const [name, setName] = useState('');
  const [error, setError] = useState<string | null>(null);
  const login = useLogin();
  const register = useRegister();
  const navigate = useNavigate();

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    try {
      if (tab === 'signin') {
        await login.mutateAsync({ email, password });
      } else {
        const trimmed = name.trim();
        await register.mutateAsync(
          trimmed ? { email, password, display_name: trimmed } : { email, password },
        );
      }
      // @ts-expect-error route added in Phase 7.2
      await navigate({ to: '/profile' });
    } catch (err) {
      if (isApiError(err)) {
        const msg =
          err.body && typeof err.body === 'object' && 'error' in err.body
            ? String((err.body as { error: unknown }).error)
            : `Request failed (${err.status})`;
        setError(msg);
      } else {
        setError('Network error');
      }
    }
  }

  const submitting = login.isPending || register.isPending;
  return (
    <form className="auth-form-wrap" onSubmit={onSubmit}>
      <h1>{tab === 'signin' ? 'Welcome back.' : 'Join the corpus.'}</h1>
      <p className="lede">
        {tab === 'signin'
          ? 'Sign in to your library, citations, and targeted searches.'
          : 'Free for individual academics. No card required.'}
      </p>
      <div className="auth-tabs">
        <button
          type="button"
          className={`auth-tab ${tab === 'signin' ? 'active' : ''}`}
          onClick={() => setTab('signin')}
        >
          Sign in
        </button>
        <button
          type="button"
          className={`auth-tab ${tab === 'signup' ? 'active' : ''}`}
          onClick={() => setTab('signup')}
        >
          Create account
        </button>
      </div>
      {tab === 'signup' && (
        <div className="field">
          <label htmlFor="name">Full name</label>
          <input
            id="name"
            type="text"
            value={name}
            onChange={(e) => setName(e.target.value)}
            placeholder="Anya Klint"
          />
        </div>
      )}
      <div className="field">
        <label htmlFor="email">Academic email</label>
        <input
          id="email"
          type="email"
          required
          autoComplete="email"
          value={email}
          onChange={(e) => setEmail(e.target.value)}
          placeholder="you@university.edu"
        />
      </div>
      <div className="field">
        <label htmlFor="password">Password</label>
        <input
          id="password"
          type="password"
          required
          autoComplete="current-password"
          minLength={8}
          value={password}
          onChange={(e) => setPassword(e.target.value)}
          placeholder="••••••••••••"
        />
      </div>
      {error && (
        <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginBottom: 12 }}>
          {error}
        </div>
      )}
      <button
        className="btn btn-primary"
        type="submit"
        disabled={submitting}
        style={{ width: '100%', justifyContent: 'center', marginTop: 8 }}
      >
        {tab === 'signin'
          ? submitting
            ? 'Signing in…'
            : 'Sign in'
          : submitting
            ? 'Creating…'
            : 'Create free account'}
      </button>
      <div className="divider">Or continue with</div>
      <div className="oauth-grid">
        {['ORCID', 'GitHub', 'Google', 'Institution SSO'].map((p) => (
          <button key={p} type="button" className="oauth-btn" disabled title="Coming soon">
            {p}
          </button>
        ))}
      </div>
      <p
        style={{
          marginTop: 32,
          fontSize: 12,
          color: 'var(--ink-500)',
          textAlign: 'center',
        }}
      >
        By continuing you agree to our terms and privacy. The corpus is free to read; we never sell
        your queries.
      </p>
    </form>
  );
}
