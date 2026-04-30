/// <reference types="vite/client" />

// Resolve API base. Three tiers, in order:
//   1. VITE_API_URL baked at build time (set explicitly by build-release.sh
//      to https://api.nasrudin.org for prod builds).
//   2. In a browser tab on a known prod hostname, derive from window.location
//      so a misconfigured build still works (a hostname starting with
//      `nasrudin.` always implies api.nasrudin.org).
//   3. Dev fallback: http://localhost:3001.
//
// The browser-derived path means any future component that goes around
// VITE_API_URL still hits the right host on prod, instead of leaking
// localhost into the production bundle.
function resolveApiBase(): string {
  const fromEnv = import.meta.env.VITE_API_URL as string | undefined;
  if (fromEnv && fromEnv.length > 0) return fromEnv;
  if (typeof window !== 'undefined') {
    const host = window.location.hostname;
    if (host === 'nasrudin.org' || host.endsWith('.nasrudin.org')) {
      return 'https://api.nasrudin.org';
    }
  }
  return 'http://localhost:3001';
}

export const API_BASE = resolveApiBase();

export class ApiError extends Error {
  constructor(
    public readonly status: number,
    public readonly body: unknown,
  ) {
    super(`API ${status}`);
  }
}

interface FetchOptions extends RequestInit {
  /** When SSR is forwarding cookies, pass them here. */
  cookieHeader?: string;
}

export async function apiFetch<T>(path: string, init: FetchOptions = {}): Promise<T> {
  const headers = new Headers(init.headers);
  headers.set('Accept', 'application/json');
  if (init.body != null && !headers.has('Content-Type')) {
    headers.set('Content-Type', 'application/json');
  }
  if (init.cookieHeader) headers.set('Cookie', init.cookieHeader);

  const res = await fetch(`${API_BASE}${path}`, {
    credentials: 'include',
    ...init,
    headers,
  });

  if (!res.ok) {
    let body: unknown = null;
    try {
      body = await res.json();
    } catch {
      /* swallow */
    }
    throw new ApiError(res.status, body);
  }
  if (res.status === 204) return undefined as T;
  return (await res.json()) as T;
}

export const isApiError = (e: unknown): e is ApiError => e instanceof ApiError;
