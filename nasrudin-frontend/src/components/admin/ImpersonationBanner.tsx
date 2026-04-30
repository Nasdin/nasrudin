/**
 * Sticky banner shown on every page when sessionStorage has an active
 * impersonation token. Counts down to expiry; on zero, calls the server
 * end endpoint and clears state. Manual "End impersonation" button does
 * the same on demand.
 */

import { useEffect, useState } from 'react';
import { adminFetch } from '~/lib/adminApi';

export default function ImpersonationBanner() {
  const [active, setActive] = useState(
    () => typeof sessionStorage !== 'undefined' && !!sessionStorage.getItem('impersonate_token'),
  );
  const [remaining, setRemaining] = useState(0);

  useEffect(() => {
    if (!active) return;
    const tick = () => {
      const exp = Number(sessionStorage.getItem('impersonate_expires_at') ?? 0);
      const r = Math.max(0, Math.floor((exp - Date.now()) / 1000));
      setRemaining(r);
      if (r <= 0) void endImpersonation(setActive);
    };
    tick();
    const id = window.setInterval(tick, 1000);
    return () => window.clearInterval(id);
  }, [active]);

  if (!active) return null;
  const target = sessionStorage.getItem('impersonate_target_email') ?? 'user';
  return (
    <div
      role="status"
      style={{
        background: 'crimson',
        color: 'white',
        padding: '10px 16px',
        position: 'sticky',
        top: 0,
        zIndex: 1000,
        display: 'flex',
        gap: 12,
        alignItems: 'center',
      }}
    >
      <strong>Impersonating</strong> <span>{target}</span>
      <span>· {remaining}s remaining ·</span>
      <button onClick={() => void endImpersonation(setActive)} style={{ marginLeft: 'auto' }}>
        End impersonation
      </button>
    </div>
  );
}

async function endImpersonation(setActive: (v: boolean) => void) {
  const sid = sessionStorage.getItem('impersonate_session_id');
  if (sid) {
    try {
      await adminFetch('/api/admin/impersonate/end', {
        method: 'POST',
        body: JSON.stringify({ session_id: sid }),
        headers: { 'Content-Type': 'application/json' },
      });
    } catch {
      // swallow — we still want to clear local state
    }
  }
  for (const k of [
    'impersonate_token',
    'impersonate_session_id',
    'impersonate_expires_at',
    'impersonate_target_email',
  ]) {
    sessionStorage.removeItem(k);
  }
  setActive(false);
  if (typeof window !== 'undefined') window.location.href = '/admin';
}
