import { useNavigate } from '@tanstack/react-router';
import { type FormEvent, useState } from 'react';
import { firebaseErrorMessage } from '~/lib/firebase';
import {
  useGoogleLogin,
  useLogin,
  useRegister,
  useResetPassword,
} from '~/lib/queries';

type Mode = 'signin' | 'signup' | 'forgot' | 'reset-sent' | 'verify-sent';

export function AuthForm() {
  const [mode, setMode] = useState<Mode>('signin');
  const [email, setEmail] = useState('');
  const [password, setPassword] = useState('');
  const [error, setError] = useState<string | null>(null);

  const login = useLogin();
  const register = useRegister();
  const google = useGoogleLogin();
  const reset = useResetPassword();
  const navigate = useNavigate();

  async function onGoogle() {
    setError(null);
    try {
      await google.mutateAsync();
      await navigate({ to: '/profile' });
    } catch (e) {
      setError(firebaseErrorMessage(e));
    }
  }

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    try {
      if (mode === 'signin') {
        await login.mutateAsync({ email, password });
        await navigate({ to: '/profile' });
      } else if (mode === 'signup') {
        const result = await register.mutateAsync({ email, password });
        if (result === null) {
          setMode('verify-sent');
        } else {
          await navigate({ to: '/profile' });
        }
      } else if (mode === 'forgot') {
        await reset.mutateAsync(email);
        setMode('reset-sent');
      }
    } catch (err) {
      setError(firebaseErrorMessage(err));
    }
  }

  const submitting =
    login.isPending || register.isPending || reset.isPending || google.isPending;

  return (
    <form className="auth-form-wrap" onSubmit={onSubmit}>
      <h1>
        {mode === 'signin' && 'Welcome back.'}
        {mode === 'signup' && 'Join the corpus.'}
        {mode === 'forgot' && 'Reset your password.'}
        {mode === 'reset-sent' && 'Check your inbox.'}
        {mode === 'verify-sent' && 'Verify your email.'}
      </h1>
      <p className="lede">
        {mode === 'signin' && 'Sign in to your library, citations, and targeted searches.'}
        {mode === 'signup' && 'Free for individual academics. No card required.'}
        {mode === 'forgot' && "We'll email you a link to set a new password."}
        {mode === 'reset-sent' &&
          `We sent a password-reset link to ${email}. The link expires in 1 hour.`}
        {mode === 'verify-sent' &&
          `We sent a verification link to ${email}. Click it, then sign in.`}
      </p>

      {(mode === 'signin' || mode === 'signup') && (
        <>
          <button
            type="button"
            className="oauth-primary"
            onClick={onGoogle}
            disabled={submitting}
          >
            <GoogleSvg />
            Continue with Google
          </button>
          <div className="divider">or</div>
          <div className="auth-tabs">
            <button
              type="button"
              className={`auth-tab ${mode === 'signin' ? 'active' : ''}`}
              onClick={() => {
                setMode('signin');
                setError(null);
              }}
            >
              Sign in
            </button>
            <button
              type="button"
              className={`auth-tab ${mode === 'signup' ? 'active' : ''}`}
              onClick={() => {
                setMode('signup');
                setError(null);
              }}
            >
              Create account
            </button>
          </div>
        </>
      )}

      {(mode === 'signin' || mode === 'signup' || mode === 'forgot') && (
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
      )}

      {(mode === 'signin' || mode === 'signup') && (
        <div className="field">
          <label htmlFor="password">Password</label>
          <input
            id="password"
            type="password"
            required
            autoComplete={mode === 'signin' ? 'current-password' : 'new-password'}
            minLength={8}
            value={password}
            onChange={(e) => setPassword(e.target.value)}
            placeholder="••••••••••••"
          />
          {mode === 'signin' && (
            <button
              type="button"
              onClick={() => {
                setMode('forgot');
                setError(null);
              }}
              style={{
                background: 'none',
                border: 'none',
                color: 'var(--ink-500)',
                fontSize: 12,
                cursor: 'pointer',
                marginTop: 6,
                padding: 0,
              }}
            >
              Forgot password?
            </button>
          )}
        </div>
      )}

      {error && (
        <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginBottom: 12 }}>
          {error}
        </div>
      )}

      {(mode === 'signin' || mode === 'signup' || mode === 'forgot') && (
        <button
          className="btn btn-primary"
          type="submit"
          disabled={submitting}
          style={{ width: '100%', justifyContent: 'center', marginTop: 8 }}
        >
          {mode === 'signin' && (submitting ? 'Signing in…' : 'Sign in')}
          {mode === 'signup' && (submitting ? 'Creating…' : 'Create free account')}
          {mode === 'forgot' && (submitting ? 'Sending…' : 'Send reset link')}
        </button>
      )}

      {(mode === 'forgot' || mode === 'reset-sent' || mode === 'verify-sent') && (
        <button
          type="button"
          onClick={() => {
            setMode('signin');
            setError(null);
          }}
          style={{
            background: 'none',
            border: 'none',
            color: 'var(--ink-500)',
            fontSize: 13,
            cursor: 'pointer',
            marginTop: 16,
          }}
        >
          ← Back to sign in
        </button>
      )}

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

function GoogleSvg() {
  return (
    <svg viewBox="0 0 18 18" aria-hidden="true">
      <path
        fill="#4285F4"
        d="M17.64 9.205c0-.639-.057-1.252-.164-1.841H9v3.481h4.844a4.14 4.14 0 0 1-1.796 2.716v2.259h2.908c1.702-1.567 2.684-3.875 2.684-6.615z"
      />
      <path
        fill="#34A853"
        d="M9 18c2.43 0 4.467-.806 5.956-2.18l-2.908-2.259c-.806.54-1.837.86-3.048.86-2.344 0-4.328-1.584-5.036-3.711H.957v2.332A8.997 8.997 0 0 0 9 18z"
      />
      <path
        fill="#FBBC05"
        d="M3.964 10.71A5.41 5.41 0 0 1 3.682 9c0-.593.102-1.17.282-1.71V4.958H.957A8.996 8.996 0 0 0 0 9c0 1.452.348 2.827.957 4.042l3.007-2.332z"
      />
      <path
        fill="#EA4335"
        d="M9 3.58c1.321 0 2.508.454 3.44 1.345l2.582-2.58C13.463.891 11.426 0 9 0A8.997 8.997 0 0 0 .957 4.958L3.964 7.29C4.672 5.163 6.656 3.58 9 3.58z"
      />
    </svg>
  );
}
