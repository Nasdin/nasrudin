import { type QueryClient, QueryClientProvider } from '@tanstack/react-query';
import { createRootRouteWithContext, HeadContent, Outlet, Scripts } from '@tanstack/react-router';
import { lazy, Suspense } from 'react';

// Devtools is a devDependency — exclude it from prod node_modules + SSR
// runtime by gating the dynamic import on import.meta.env.DEV. Vite
// tree-shakes the dynamic import branch when DEV is false at build time.
const ReactQueryDevtools = import.meta.env.DEV
  ? lazy(() =>
      import('@tanstack/react-query-devtools').then((m) => ({ default: m.ReactQueryDevtools })),
    )
  : null;

// Bare `import '...css'` no longer reaches the SSR'd HTML in
// @tanstack/react-start 1.167+ — the build collects the CSS into a
// hashed asset but the <link rel="stylesheet"> is never injected into
// <head>, so the entire site loads as unstyled HTML on first paint.
// Importing as ?url forces Vite to give us the resolved asset URL,
// which we then declare in `head.links` below so it ships in SSR.
import tokensCss from '~/styles/tokens.css?url';
import stylesCss from '~/styles/styles.css?url';
import platformCss from '~/styles/platform.css?url';
// KaTeX CSS is loaded by `src/lib/katex-inner.tsx` (lazy) — only routes
// that actually render math pull it in.

interface RouterContext {
  queryClient: QueryClient;
}

export const Route = createRootRouteWithContext<RouterContext>()({
  head: () => ({
    meta: [
      { charSet: 'utf-8' },
      { name: 'viewport', content: 'width=device-width, initial-scale=1' },
      { title: 'Nasrudin — derive physics from pure logic' },
    ],
    links: [
      { rel: 'stylesheet', href: tokensCss },
      { rel: 'stylesheet', href: stylesCss },
      { rel: 'stylesheet', href: platformCss },
      { rel: 'icon', type: 'image/svg+xml', href: '/favicon.svg' },
    ],
  }),
  component: RootDocument,
});

function RootDocument() {
  const { queryClient } = Route.useRouteContext();
  return (
    <html lang="en">
      <head>
        <HeadContent />
      </head>
      <body>
        <QueryClientProvider client={queryClient}>
          <Outlet />
          {ReactQueryDevtools && (
            <Suspense fallback={null}>
              <ReactQueryDevtools initialIsOpen={false} />
            </Suspense>
          )}
        </QueryClientProvider>
        <Scripts />
      </body>
    </html>
  );
}
