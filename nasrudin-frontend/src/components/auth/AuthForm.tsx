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

      <a href="/api/auth/github/start" className="oauth-primary">
        <svg viewBox="0 0 24 24" aria-hidden="true">
          <path d="M12 .3a12 12 0 0 0-3.79 23.4c.6.11.82-.26.82-.58v-2.05c-3.34.73-4.04-1.61-4.04-1.61-.55-1.39-1.34-1.76-1.34-1.76-1.09-.74.08-.73.08-.73 1.21.09 1.85 1.24 1.85 1.24 1.07 1.84 2.81 1.31 3.5 1 .11-.78.42-1.31.76-1.61-2.66-.3-5.46-1.33-5.46-5.93 0-1.31.47-2.38 1.24-3.22-.13-.3-.54-1.52.11-3.18 0 0 1-.32 3.3 1.23a11.5 11.5 0 0 1 6 0c2.3-1.55 3.3-1.23 3.3-1.23.65 1.66.24 2.88.12 3.18.77.84 1.24 1.91 1.24 3.22 0 4.61-2.81 5.62-5.49 5.92.43.37.81 1.1.81 2.22v3.29c0 .32.22.7.83.58A12 12 0 0 0 12 .3" />
        </svg>
        Continue with GitHub
      </a>

      <div className="divider">or</div>

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
