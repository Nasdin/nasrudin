# Research Report: TanStack Start createServerFn + Route Loaders + TanStack Query Integration
Generated: 2026-01-31

## Summary

TanStack Start's `createServerFn` provides server-only RPC functions that are called seamlessly from client code. Route loaders are **isomorphic** (run on server during SSR, on client during SPA navigation), so server functions must be used inside loaders to keep secrets safe. The recommended pattern combines `createServerFn` for data fetching, `queryOptions` for cache configuration, `ensureQueryData` in loaders for prefetching, and `useSuspenseQuery` in components for rendering.

---

## Questions Answered

### Q1: How does createServerFn work (syntax, options, validator)?

**Answer:** `createServerFn` is imported from `@tanstack/react-start`. It uses a builder/chaining pattern.

**Source:** [Server Functions Docs](https://tanstack.com/start/latest/docs/framework/react/guide/server-functions)
**Confidence:** High

**Core syntax:**

```ts
import { createServerFn } from '@tanstack/react-start'

// Minimal - GET by default
export const getTime = createServerFn().handler(async () => {
  return new Date().toISOString()
})

// With HTTP method
export const saveItem = createServerFn({ method: 'POST' }).handler(async () => {
  // server-only code
})

// With input validation (plain function)
export const getUser = createServerFn({ method: 'GET' })
  .inputValidator((data: { id: string }) => data)
  .handler(async ({ data }) => {
    return findUserById(data.id)
  })

// With Zod validation
import { z } from 'zod'

export const createUser = createServerFn({ method: 'POST' })
  .inputValidator(z.object({
    name: z.string().min(1),
    age: z.number().min(0),
  }))
  .handler(async ({ data }) => {
    // data is typed as { name: string; age: number }
    return insertUser(data)
  })

// With middleware
export const protectedAction = createServerFn({ method: 'POST' })
  .middleware([authMiddleware])
  .inputValidator(schema)
  .handler(async ({ data, context }) => {
    // context comes from middleware
  })
```

**Key details:**
- `method: 'GET'` is the default. Use `'POST'` for mutations.
- `.inputValidator()` validates the single `data` parameter crossing the network boundary.
- `.handler()` receives `{ data }` (validated input) and runs **only on the server**.
- The build process replaces server function implementations with RPC stubs in client bundles.
- You can access request/response via helpers from `@tanstack/react-start/server`:
  ```ts
  import { getRequest, getRequestHeader, setResponseHeaders, setResponseStatus } from '@tanstack/react-start/server'
  ```

**Calling a server function:**
```ts
// Without input
const time = await getTime()

// With input
const user = await getUser({ data: { id: '123' } })
```

**Note:** The older API used `.validator()` -- the current API uses `.inputValidator()`.

---

### Q2: How to use server functions inside route loaders for data fetching

**Answer:** Loaders are isomorphic, so you MUST wrap sensitive operations (DB calls, API calls with secrets) in `createServerFn`. The server function is then called from the loader.

**Source:** [Execution Model Docs](https://tanstack.com/start/latest/docs/framework/react/guide/execution-model), [Code Execution Patterns](https://tanstack.com/start/latest/docs/framework/react/guide/code-execution-patterns)
**Confidence:** High

**Pattern 1: Direct server function in loader (simple, no caching)**

```ts
// src/routes/theorems.tsx
import { createFileRoute } from '@tanstack/react-router'
import { createServerFn } from '@tanstack/react-start'

const fetchTheorems = createServerFn({ method: 'GET' }).handler(async () => {
  // This runs ONLY on the server - safe for secrets
  const res = await fetch(`${process.env.ENGINE_API_URL}/theorems`, {
    headers: { Authorization: `Bearer ${process.env.API_KEY}` }
  })
  return res.json()
})

export const Route = createFileRoute('/theorems')({
  loader: async () => await fetchTheorems(),
  component: TheoremsPage,
})

function TheoremsPage() {
  const theorems = Route.useLoaderData()
  return <div>{/* render theorems */}</div>
}
```

**Pattern 2: Server function + TanStack Query (recommended for caching)**

```ts
// src/server/theorems.functions.ts
import { createServerFn } from '@tanstack/react-start'

export const fetchTheorems = createServerFn({ method: 'GET' }).handler(async () => {
  const res = await fetch(`${process.env.ENGINE_API_URL}/theorems`)
  return res.json()
})

export const fetchTheorem = createServerFn({ method: 'GET' })
  .inputValidator((data: { id: string }) => data)
  .handler(async ({ data }) => {
    const res = await fetch(`${process.env.ENGINE_API_URL}/theorems/${data.id}`)
    return res.json()
  })
```

```ts
// src/lib/queries.ts
import { queryOptions } from '@tanstack/react-query'
import { fetchTheorems, fetchTheorem } from '../server/theorems.functions'

export const theoremsQueryOptions = () => queryOptions({
  queryKey: ['theorems'],
  queryFn: () => fetchTheorems(),
  staleTime: 30_000,
})

export const theoremQueryOptions = (id: string) => queryOptions({
  queryKey: ['theorem', id],
  queryFn: () => fetchTheorem({ data: { id } }),
  staleTime: 60_000,
})
```

```ts
// src/routes/theorems.tsx
import { createFileRoute } from '@tanstack/react-router'
import { useSuspenseQuery } from '@tanstack/react-query'
import { theoremsQueryOptions } from '../lib/queries'

export const Route = createFileRoute('/theorems')({
  loader: async ({ context }) => {
    await context.queryClient.ensureQueryData(theoremsQueryOptions())
  },
  component: TheoremsPage,
})

function TheoremsPage() {
  const { data: theorems } = useSuspenseQuery(theoremsQueryOptions())
  return <div>{/* render theorems */}</div>
}
```

**CRITICAL: Why you need server functions in loaders:**

Loaders are isomorphic. They run:
- On the **server** during SSR (initial page load)
- On the **client** during SPA navigation (link clicks)

If you put `process.env.SECRET_KEY` directly in a loader, it will leak to the client bundle. `createServerFn` ensures the code stays server-only -- on the client, calls become `fetch()` requests to the server.

---

### Q3: Best practices for combining createServerFn with TanStack Query

**Answer:** The recommended stack is: `createServerFn` (data fetching) -> `queryOptions` (cache config) -> `ensureQueryData` in loader (prefetch) -> `useSuspenseQuery` in component (render).

**Source:** [TanStack Query Integration Docs](https://tanstack.com/router/latest/docs/integrations/query), [Using Server Functions and TanStack Query](https://www.brenelz.com/posts/using-server-functions-and-tanstack-query/)
**Confidence:** High

**Step 1: Set up router with `routerWithQueryClient`**

This is what the project is currently missing. The `@tanstack/react-router-ssr-query` package (already in `package.json`) provides this:

```ts
// src/router.tsx
import { QueryClient } from '@tanstack/react-query'
import { createRouter as createTanStackRouter } from '@tanstack/react-router'
import { routerWithQueryClient } from '@tanstack/react-router-ssr-query'
import { routeTree } from './routeTree.gen'

export function createRouter() {
  const queryClient = new QueryClient({
    defaultOptions: {
      queries: { staleTime: 30_000 },
    },
  })

  return routerWithQueryClient(
    createTanStackRouter({
      routeTree,
      context: { queryClient },
      scrollRestoration: true,
      defaultPreload: 'intent',
      defaultPreloadStaleTime: 0,
    }),
    queryClient,
  )
}
```

**Why `routerWithQueryClient`?** It handles dehydration/rehydration of query data between server and client during SSR. Without it, data fetched on the server won't transfer to the client's QueryClient.

**Step 2: Root route with typed context**

```ts
// src/routes/__root.tsx
import type { QueryClient } from '@tanstack/react-query'
import { createRootRouteWithContext } from '@tanstack/react-router'

interface RouterContext {
  queryClient: QueryClient
}

export const Route = createRootRouteWithContext<RouterContext>()({
  // ...
})
```

**Step 3: Define queryOptions with server functions**

```ts
// src/lib/queries.ts
import { queryOptions } from '@tanstack/react-query'
import { fetchStats } from '../server/engine.functions'

export const statsQueryOptions = () => queryOptions({
  queryKey: ['stats'],
  queryFn: () => fetchStats(),
  staleTime: 30_000,
})
```

**Step 4: Use in loader + component**

```ts
export const Route = createFileRoute('/dashboard')({
  loader: async ({ context: { queryClient } }) => {
    // ensureQueryData: fetch only if not in cache
    await queryClient.ensureQueryData(statsQueryOptions())
  },
  component: Dashboard,
})

function Dashboard() {
  // useSuspenseQuery: never returns undefined, participates in SSR streaming
  const { data } = useSuspenseQuery(statsQueryOptions())
  return <div>{data.total_theorems} theorems</div>
}
```

**Step 5: Parallel prefetching for multiple queries**

```ts
loader: async ({ context: { queryClient } }) => {
  // Parallel - don't create a waterfall
  await Promise.allSettled([
    queryClient.ensureQueryData(statsQueryOptions()),
    queryClient.ensureQueryData(theoremsQueryOptions()),
  ])
}
```

**Step 6: Deferred (non-blocking) data**

```ts
loader: async ({ context: { queryClient } }) => {
  // Critical data - block render
  await queryClient.ensureQueryData(criticalDataOptions())

  // Non-critical - start fetch but don't await
  queryClient.prefetchQuery(secondaryDataOptions())
}
```

**TypeScript tip:** To avoid slow TS inference with complex return types:

```ts
loader: async ({ context: { queryClient } }) => {
  // await returns void, not the data type - better for TS perf
  await queryClient.ensureQueryData(theoremsQueryOptions())
}
```

---

### Q4: How loaders work in TanStack Start (isomorphic execution)

**Answer:** Loaders run on the server during SSR and on the client during SPA navigation. `beforeLoad` runs sequentially (parent-to-child); `loader` runs in parallel across siblings.

**Source:** [Execution Model](https://tanstack.com/start/latest/docs/framework/react/guide/execution-model), [TanStack Start Loaders Explained](https://www.anchortags.dev/posts/tanstack-start-loaders-explained)
**Confidence:** High

**Execution flow:**

```
Initial Page Load (SSR):
  Server: beforeLoad (sequential, parent→child)
  Server: loader (parallel across siblings)
  Server: Render component with data
  Server: Stream HTML + dehydrated state to client
  Client: Hydrate, reuse server data

SPA Navigation (client-side):
  Client: beforeLoad (sequential, parent→child)
  Client: loader (parallel across siblings)
  Client: Render component with data
```

**Key behaviors:**
1. ALL active route loaders re-run on navigation, not just the target route. For `/layout/dashboard/settings`, navigating within changes re-runs all three loaders.
2. Return values must be serializable (since they cross the server→client boundary during SSR). Promises are allowed and can be streamed.
3. `router.invalidate()` re-runs all active loaders.

**SSR modes per route:**

```ts
// Full SSR (default) - loader + render on server
export const Route = createFileRoute('/page')({
  ssr: true,  // default
  loader: ...,
  component: ...,
})

// Data-only - loader on server, component renders client-side only
export const Route = createFileRoute('/page')({
  ssr: 'data-only',
  loader: ...,
  component: ...,
})

// SPA mode - nothing runs on server
export const Route = createFileRoute('/page')({
  ssr: false,
  loader: ...,
  component: ...,
})
```

**`loaderDeps` for search-param-dependent loaders:**

```ts
export const Route = createFileRoute('/search')({
  loaderDeps: ({ search }) => ({
    query: search.q,
    page: search.page,
  }),
  loader: async ({ deps: { query, page }, context: { queryClient } }) => {
    await queryClient.ensureQueryData(searchQueryOptions(query, page))
  },
  component: SearchPage,
})
```

---

### Q5: pendingComponent and errorComponent patterns

**Answer:** `pendingComponent` shows during loader delays (after `pendingMs` threshold). `errorComponent` catches loader/beforeLoad errors per route.

**Source:** [Data Loading Docs](https://tanstack.com/router/v1/docs/framework/react/guide/data-loading), [Error Boundaries](https://tanstack.com/start/latest/docs/framework/react/guide/error-boundaries)
**Confidence:** High

**pendingComponent:**

```ts
export const Route = createFileRoute('/theorems')({
  loader: async ({ context }) => {
    await context.queryClient.ensureQueryData(theoremsQueryOptions())
  },
  pendingMs: 200,       // Show pending after 200ms of loading
  pendingMinMs: 500,    // Keep pending visible for at least 500ms (prevents flash)
  pendingComponent: () => (
    <div className="p-8 max-w-3xl mx-auto">
      <div className="animate-pulse space-y-4">
        <div className="h-6 bg-slate-200 rounded w-1/3" />
        <div className="h-40 bg-slate-100 rounded-xl" />
      </div>
    </div>
  ),
  component: TheoremsPage,
})
```

**Router-level defaults:**

```ts
const router = createRouter({
  routeTree,
  context: { queryClient },
  defaultPendingComponent: () => (
    <div className="flex items-center justify-center p-8">
      <div className="animate-spin h-8 w-8 border-2 border-slate-300 border-t-slate-600 rounded-full" />
    </div>
  ),
  defaultPendingMs: 200,
  defaultPendingMinMs: 300,
})
```

**errorComponent:**

```ts
export const Route = createFileRoute('/theorem/$theoremId')({
  loader: async ({ params, context }) => {
    await context.queryClient.ensureQueryData(
      theoremQueryOptions(params.theoremId)
    )
  },
  errorComponent: ({ error, reset }) => (
    <div className="p-8 text-center">
      <h2 className="text-xl font-bold text-red-600 mb-2">
        Failed to load theorem
      </h2>
      <p className="text-slate-500 mb-4">{error.message}</p>
      <button
        onClick={reset}
        className="px-4 py-2 bg-blue-600 text-white rounded hover:bg-blue-700"
      >
        Try Again
      </button>
    </div>
  ),
  component: TheoremDetailPage,
})
```

**Router-level default:**

```ts
const router = createRouter({
  routeTree,
  context: { queryClient },
  defaultErrorComponent: ({ error, reset }) => (
    <div className="p-8 text-center">
      <h2 className="text-xl font-bold text-red-600">Something went wrong</h2>
      <pre className="text-sm text-slate-500 mt-2">{error.message}</pre>
      <button onClick={reset} className="mt-4 text-blue-600 underline">
        Retry
      </button>
    </div>
  ),
})
```

**`notFoundComponent`** (related):

```ts
export const Route = createFileRoute('/theorem/$theoremId')({
  loader: async ({ params, context }) => {
    const data = await context.queryClient.ensureQueryData(
      theoremQueryOptions(params.theoremId)
    )
    if (!data) {
      throw notFound()
    }
  },
  notFoundComponent: () => (
    <div className="p-8 text-center">
      <h2 className="text-xl font-bold">Theorem not found</h2>
    </div>
  ),
})
```

**Known caveats (2025):**
- `pendingComponent` may not show on initial SSR page load for the root route (GitHub issue #2182).
- `errorComponent` from `beforeLoad` errors may be ignored on the very first SSR request (GitHub issue #3462).
- Routes without a `loader`/`beforeLoad` won't trigger `pendingComponent` even during code-split chunk loading (GitHub issue #3556).

---

## Detailed Findings: Current Codebase Analysis

### Finding 1: Current router.tsx does not use routerWithQueryClient

**File:** `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/router.tsx`

The current setup creates a plain `createRouter` and manually passes `queryClient` via context. However, it does NOT use `routerWithQueryClient` from `@tanstack/react-router-ssr-query` (which IS already a dependency in package.json at version `^1.157.16`).

Without `routerWithQueryClient`, query data fetched on the server during SSR will NOT be dehydrated and sent to the client -- meaning the client will re-fetch everything on hydration.

### Finding 2: Routes use client-side useQuery instead of loader prefetching

**Files:** `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/routes/domains/index.tsx`, `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/routes/theorem/$theoremId.tsx`

Current routes have no `loader` function and fetch data in components via `useQuery`. This means:
- No SSR data (empty page until client JS hydrates and fetches)
- No prefetching on hover
- Manual loading/error state handling in every component

### Finding 3: Server functions already exist in demos

**File:** `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/routes/demo/start.server-funcs.tsx`

The demo shows the correct pattern: `createServerFn` -> loader -> `useLoaderData`. But it uses raw loader data instead of TanStack Query integration.

### Finding 4: API calls use relative /api paths

**File:** `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/lib/api.ts`

The `apiFetch` function uses `const API_BASE = "/api"` -- relative URLs. These work from both server and client if the server has proper proxy/middleware. For server functions, you may need to use an absolute URL (e.g., `http://localhost:8080/api`) since the server-side fetch won't have a browser origin.

---

## Recommended Migration Pattern for This Codebase

### Step 1: Update router.tsx

```ts
import { QueryClient } from '@tanstack/react-query'
import { createRouter as createTanStackRouter } from '@tanstack/react-router'
import { routerWithQueryClient } from '@tanstack/react-router-ssr-query'
import { routeTree } from './routeTree.gen'

export function createRouter() {
  const queryClient = new QueryClient({
    defaultOptions: {
      queries: { staleTime: 30_000 },
    },
  })

  return routerWithQueryClient(
    createTanStackRouter({
      routeTree,
      context: { queryClient },
      scrollRestoration: true,
      defaultPreload: 'intent',
      defaultPreloadStaleTime: 0,
      defaultPendingMs: 200,
      defaultPendingMinMs: 300,
      defaultPendingComponent: () => (
        <div className="flex items-center justify-center p-8">
          <div className="animate-spin h-8 w-8 border-2 border-slate-300 border-t-slate-600 rounded-full" />
        </div>
      ),
    }),
    queryClient,
  )
}
```

### Step 2: Create server functions for API calls

```ts
// src/server/engine.functions.ts
import { createServerFn } from '@tanstack/react-start'

const ENGINE_API = process.env.ENGINE_API_URL ?? 'http://localhost:8080'

export const fetchStats = createServerFn({ method: 'GET' }).handler(async () => {
  const res = await fetch(`${ENGINE_API}/api/stats`)
  if (!res.ok) throw new Error(`API error: ${res.status}`)
  return res.json()
})

export const fetchTheorem = createServerFn({ method: 'GET' })
  .inputValidator((data: { id: string }) => data)
  .handler(async ({ data }) => {
    const res = await fetch(`${ENGINE_API}/api/theorems/${data.id}`)
    if (!res.ok) throw new Error(`API error: ${res.status}`)
    return res.json()
  })

export const searchTheorems = createServerFn({ method: 'GET' })
  .inputValidator((data: { domain?: string; latex?: string; limit?: number; offset?: number }) => data)
  .handler(async ({ data }) => {
    const params = new URLSearchParams()
    if (data.domain) params.set('domain', data.domain)
    if (data.latex) params.set('latex', data.latex)
    if (data.limit) params.set('limit', String(data.limit))
    if (data.offset) params.set('offset', String(data.offset))
    const res = await fetch(`${ENGINE_API}/api/theorems?${params}`)
    if (!res.ok) throw new Error(`API error: ${res.status}`)
    return res.json()
  })
```

### Step 3: Update queryOptions to use server functions

```ts
// src/lib/queries.ts
import { queryOptions } from '@tanstack/react-query'
import { fetchStats, fetchTheorem, searchTheorems } from '../server/engine.functions'

export const statsQueryOptions = () => queryOptions({
  queryKey: ['stats'],
  queryFn: () => fetchStats(),
  staleTime: 30_000,
})

export const theoremQueryOptions = (id: string) => queryOptions({
  queryKey: ['theorem', id],
  queryFn: () => fetchTheorem({ data: { id } }),
  staleTime: 60_000,
})
```

### Step 4: Add loaders to routes

```ts
// src/routes/theorem/$theoremId.tsx
import { createFileRoute } from '@tanstack/react-router'
import { useSuspenseQuery } from '@tanstack/react-query'
import { theoremQueryOptions } from '../../lib/queries'

export const Route = createFileRoute('/theorem/$theoremId')({
  loader: async ({ params, context: { queryClient } }) => {
    await queryClient.ensureQueryData(theoremQueryOptions(params.theoremId))
  },
  errorComponent: ({ error, reset }) => (
    <div className="p-8 text-center">
      <h2 className="text-xl font-bold text-red-600">Failed to load theorem</h2>
      <p className="text-slate-500 mt-2">{error.message}</p>
      <button onClick={reset} className="mt-4 text-blue-600 underline">Retry</button>
    </div>
  ),
  component: TheoremDetailPage,
})

function TheoremDetailPage() {
  const { theoremId } = Route.useParams()
  // No loading state needed -- ensureQueryData guarantees data is available
  const { data: theorem } = useSuspenseQuery(theoremQueryOptions(theoremId))
  return <div>{/* render */}</div>
}
```

---

## File Organization Recommendation

```
src/
  server/
    engine.functions.ts    -- createServerFn wrappers for engine API
    engine.server.ts       -- server-only helpers (if needed)
  lib/
    queries.ts             -- queryOptions definitions (using server fns as queryFn)
    types.ts               -- shared types
    api.ts                 -- can be deprecated; logic moves to server functions
  routes/
    __root.tsx             -- createRootRouteWithContext<{ queryClient }>
    theorem/$theoremId.tsx -- loader + useSuspenseQuery
    domains/index.tsx      -- loader + useSuspenseQuery
    ...
```

---

## Sources

1. [Server Functions | TanStack Start Docs](https://tanstack.com/start/latest/docs/framework/react/guide/server-functions) - Official createServerFn API docs
2. [Execution Model | TanStack Start Docs](https://tanstack.com/start/latest/docs/framework/react/guide/execution-model) - Isomorphic loader behavior
3. [Code Execution Patterns | TanStack Start Docs](https://tanstack.com/start/latest/docs/framework/react/guide/code-execution-patterns) - Server vs client code boundaries
4. [TanStack Query Integration | TanStack Router Docs](https://tanstack.com/router/latest/docs/integrations/query) - routerWithQueryClient, ensureQueryData patterns
5. [Data Loading | TanStack Router Docs](https://tanstack.com/router/v1/docs/framework/react/guide/data-loading) - Loader lifecycle, pendingComponent, errorComponent
6. [Calling an External API | TanStack Start Tutorial](https://tanstack.com/start/latest/docs/framework/react/tutorial/fetching-external-api) - Server function + external API pattern
7. [Using Server Functions and TanStack Query](https://www.brenelz.com/posts/using-server-functions-and-tanstack-query/) - Community guide on integration
8. [TanStack Start Loaders Explained](https://www.anchortags.dev/posts/tanstack-start-loaders-explained) - Deep dive on loader behavior
9. [Tanstack Start Deep Dive](https://nikuscs.com/blog/06-tanstack-start-deep-dive/) - Comprehensive framework overview
10. [Selective SSR | TanStack Start Docs](https://tanstack.com/start/latest/docs/framework/react/guide/selective-ssr) - SSR modes (true, data-only, false)
11. [Error Boundaries | TanStack Start Docs](https://tanstack.com/start/latest/docs/framework/react/guide/error-boundaries) - errorComponent patterns
12. [External Data Loading | TanStack Router Docs](https://tanstack.com/router/v1/docs/framework/react/guide/external-data-loading) - ensureQueryData vs prefetchQuery

## Open Questions

- The current `apiFetch` uses relative `/api` paths. When called from a server function, the fetch runs on the Node server where there is no browser origin. Need to confirm whether the Nitro/Vinxi server proxies these or if absolute URLs are required.
- `routerWithQueryClient` handles dehydration, but need to verify it works correctly with the project's custom `getQueryClient()` singleton pattern (SSR creates new client each time, browser reuses).
