import { dehydrate, hydrate, QueryClient } from '@tanstack/react-query';
import { createRouter as createTanstackRouter } from '@tanstack/react-router';
import { routeTree } from './routeTree.gen';

export function createRouter() {
  const queryClient = new QueryClient({
    defaultOptions: {
      queries: {
        staleTime: 30_000,
        gcTime: 5 * 60_000, // 5 minutes
        retry: (failureCount, error) => {
          // Don't retry on 401/403/404 errors
          if (error && typeof error === 'object' && 'status' in error) {
            const status = (error as { status: number }).status;
            if ([401, 403, 404].includes(status)) return false;
          }
          // Retry up to 3 times for other errors
          return failureCount < 3;
        },
        refetchOnWindowFocus: false,
        refetchOnReconnect: true,
      },
      mutations: {
        retry: 1,
      },
    },
  });
  return createTanstackRouter({
    routeTree,
    context: { queryClient },
    defaultPreload: 'intent',
    scrollRestoration: true,
    // Serialize the queryClient cache into the SSR'd HTML so the
    // client picks up the same data on hydration. Without this, the
    // server renders rows from prefetched queries (e.g. /api/domains
    // → 1655 in Electromagnetism) while the client mounts with an
    // empty cache and renders 0 — React then throws #418 (hydration
    // text mismatch) and bails out of hydration entirely, leaving
    // the page as a frozen SSR snapshot with no React running.
    // biome-ignore lint/suspicious/noExplicitAny: TanStack Router's
    // Serializable constraint rejects DehydratedState because
    // `mutationKey: readonly unknown[]` isn't statically verifiable.
    // The runtime path is fine — JSON.stringify handles it. Cast
    // to any to bypass the type-level check.
    dehydrate: (() => ({ queryClientState: dehydrate(queryClient) })) as any,
    // biome-ignore lint/suspicious/noExplicitAny: see dehydrate above.
    // Defensive: hydrate may throw on partial/empty payloads (e.g.
    // routes without a loader serialize an empty cache state). A throw
    // here aborts React mount entirely — page becomes a frozen SSR
    // snapshot with no interactivity. Swallow + warn so /search,
    // /search/concept, /pricing etc. (routes with no prefetched data)
    // still mount cleanly.
    hydrate: ((data: { queryClientState?: ReturnType<typeof dehydrate> }) => {
      try {
        if (data?.queryClientState) {
          hydrate(queryClient, data.queryClientState);
        }
      } catch (e) {
        if (typeof console !== 'undefined') console.warn('queryClient hydrate failed:', e);
      }
    }) as any,
    defaultErrorComponent: ({ error }) => (
      <div style={{ padding: '64px', textAlign: 'center' }}>
        <h1 style={{ fontSize: 24, marginBottom: 16 }}>Something went wrong</h1>
        <p style={{ color: 'var(--ink-500)', marginBottom: 24 }}>
          {error instanceof Error ? error.message : 'An unexpected error occurred'}
        </p>
        <button
          type="button"
          onClick={() => window.location.reload()}
          style={{
            padding: '8px 16px',
            background: 'var(--terracotta-600)',
            color: 'white',
            border: 'none',
            borderRadius: 4,
            cursor: 'pointer',
          }}
        >
          Reload page
        </button>
      </div>
    ),
  });
}

// TanStack Start v1.157+ requires the router entry to export `getRouter`.
export function getRouter() {
  return createRouter();
}

declare module '@tanstack/react-router' {
  interface Register {
    router: ReturnType<typeof createRouter>;
  }
}
