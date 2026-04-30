/**
 * Thin wrapper over `apiFetch` for admin endpoints. Threads the
 * impersonation token from `sessionStorage` when present (so server-side
 * impersonation_layer can substitute the AuthUser), and on 403 redirects
 * back to /.
 */

import { apiFetch, ApiError } from './api';

const IMPERSONATE_TOKEN_KEY = 'impersonate_token';

export async function adminFetch<T>(path: string, init: RequestInit = {}): Promise<T> {
  const headers = new Headers(init.headers);
  if (typeof sessionStorage !== 'undefined') {
    const token = sessionStorage.getItem(IMPERSONATE_TOKEN_KEY);
    if (token) headers.set('X-Impersonate-Token', token);
  }
  try {
    return await apiFetch<T>(path, { ...init, headers });
  } catch (e) {
    if (e instanceof ApiError && e.status === 403) {
      const body = e.body as { error?: string } | null;
      if (body?.error === 'admin_required' || body?.error === 'cannot_during_impersonation') {
        if (typeof window !== 'undefined') window.location.href = '/';
      }
    }
    throw e;
  }
}
