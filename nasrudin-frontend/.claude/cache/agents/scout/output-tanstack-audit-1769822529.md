# TanStack Library Audit Report
Generated: 2026-01-31

## Executive Summary

The frontend uses TanStack React Query and React Router effectively, but has several **unused packages** and **missing optimizations**. The main issues:

1. **5 TanStack packages installed but NOT used**: react-start, react-store, store, router-plugin, devtools-vite
2. **Missing SSR-Query integration** - not using `routerWithQueryClient`
3. **Manual debouncing** - could use `@tanstack/pacer` (not installed)
4. **No virtualization** - long theorem lists don't use `@tanstack/react-virtual`
5. **Query hooks don't follow queryOptions pattern optimally** - missing prefetch opportunities

---

## 1. package.json Analysis

### ✅ USED Packages

| Package | Version | Usage |
|---------|---------|-------|
| `@tanstack/react-query` | ^5.90.20 | ✓ Core query hooks in `queries.ts` |
| `@tanstack/react-query-devtools` | ^5.91.2 | ✓ DevTools (not visible in code but valid) |
| `@tanstack/react-router` | ^1.157.16 | ✓ Router in `router.tsx`, `__root.tsx` |
| `@tanstack/react-router-devtools` | ^1.157.16 | ✓ DevTools (not visible but valid) |
| `@tanstack/react-virtual` | ^3.13.18 | ❌ **INSTALLED BUT NOT USED** |
| `@tanstack/react-devtools` | ^0.9.3 | ✓ General devtools |

### ❌ UNUSED Packages (Remove These)

| Package | Version | Why Unused |
|---------|---------|------------|
| `@tanstack/react-router-ssr-query` | ^1.157.16 | **Not imported anywhere** - should be used in `router.tsx` |
| `@tanstack/react-start` | ^1.157.16 | **Not imported** - meta-framework features unused |
| `@tanstack/react-store` | ^0.8.0 | **Not imported** - state management unused |
| `@tanstack/store` | ^0.8.0 | **Not imported** - core store unused |
| `@tanstack/router-plugin` | ^1.157.16 | **Not used in vite.config** - build plugin unused |

### Dev Dependencies

| Package | Status |
|---------|--------|
| `@tanstack/devtools-vite` | ^0.4.1 | ❌ **Unused in vite.config** |

**Recommendation**: Remove 6 packages, saving ~1.5MB in node_modules.

---

## 2. router.tsx - Missing SSR-Query Integration

### Current Implementation

```typescript
// router.tsx
import { QueryClient } from "@tanstack/react-query";
import { createRouter } from "@tanstack/react-router";

export const getRouter = () => {
  const queryClient = getQueryClient();
  
  const router = createRouter({
    routeTree,
    context: { queryClient },
    scrollRestoration: true,
    defaultPreloadStaleTime: 0,
  });
  
  return router;
};
```

### ❌ Problem

- **NOT using `@tanstack/react-router-ssr-query`** despite having it installed
- Manual `QueryClient` creation without SSR hydration utilities
- No `routerWithQueryClient` wrapper

### ✅ Optimal Pattern

```typescript
import { routerWithQueryClient } from "@tanstack/react-router-ssr-query";
import { QueryClient } from "@tanstack/react-query";

function makeQueryClient() {
  return new QueryClient({
    defaultOptions: {
      queries: { staleTime: 30_000 },
      mutations: { onError: /* ... */ }
    },
  });
}

export const getRouter = () => {
  return routerWithQueryClient(
    createRouter({
      routeTree,
      scrollRestoration: true,
      defaultPreloadStaleTime: 0,
    }),
    makeQueryClient
  );
};
```

### Benefits

1. Automatic SSR dehydration/hydration
2. Proper query cache serialization
3. Avoids double-fetching on client hydration
4. Type-safe context integration

---

## 3. routes/__root.tsx - QueryClientProvider Setup

### Current Implementation

```typescript
function RootLayout() {
  const { queryClient } = Route.useRouteContext();
  
  return (
    <QueryClientProvider client={queryClient}>
      {/* ... */}
    </QueryClientProvider>
  );
}
```

### ✅ What's Correct

- Context-based QueryClient injection
- Clean provider wrapping

### ⚠️ Potential Issue

With `routerWithQueryClient`, the provider setup might become redundant or need adjustment. The SSR-query integration handles this internally.

### Recommendation

After adopting `routerWithQueryClient`, verify if `QueryClientProvider` is still needed or if it's automatically provided.

---

## 4. lib/queries.ts - Query Hooks Pattern

### Current Implementation

All hooks use `queryOptions` wrapped in `useQuery`:

```typescript
export function useTheorem(id: string) {
  return useQuery(
    queryOptions({
      queryKey: ["theorem", id],
      queryFn: () => apiFetch<ApiTheorem>(`/theorems/${id}`),
      staleTime: 60_000,
      enabled: !!id,
      retry: shouldRetry,
    }),
  );
}
```

### ✅ What's Correct

- Consistent `queryOptions` pattern
- Shared retry logic (`shouldRetry`)
- Proper `staleTime` configuration
- Type-safe query functions

### ❌ What's Missing

#### A. No Exported Query Options for Prefetching

**Current**: Query options are locked inside hooks

**Better**:
```typescript
// Export options separately
export const theoremQueryOptions = (id: string) =>
  queryOptions({
    queryKey: ["theorem", id],
    queryFn: () => apiFetch<ApiTheorem>(`/theorems/${id}`),
    staleTime: 60_000,
    enabled: !!id,
    retry: shouldRetry,
  });

// Hook uses exported options
export function useTheorem(id: string) {
  return useQuery(theoremQueryOptions(id));
}
```

**Why**: Enables route-level prefetching:

```typescript
// In route file
export const Route = createFileRoute("/theorem/$theoremId")({
  loader: ({ context, params }) => {
    context.queryClient.ensureQueryData(
      theoremQueryOptions(params.theoremId)
    );
  },
  component: TheoremDetail,
});
```

#### B. No Route-Level Prefetching

**Current**: Data loads AFTER navigation

**Better**: Preload on hover/navigation start
- Use `loader` in route definitions
- Prefetch on Link hover with `preload="intent"`
- Warm cache before user sees loading state

### Specific Opportunities

| Query | Prefetch Opportunity |
|-------|---------------------|
| `useTheorem` | Prefetch on TheoremCard hover |
| `useSearchTheorems` | Debounce + prefetch on input change |
| `useDomains` | Prefetch on homepage load |
| `useLineage` | Prefetch when theorem detail loads |

---

## 5. Manual Debouncing - Could Use @tanstack/pacer

### Current Pattern (3 files)

#### index.tsx
```typescript
const [query, setQuery] = useState("");
const [debouncedQuery, setDebouncedQuery] = useState("");

useEffect(() => {
  const t = setTimeout(() => setDebouncedQuery(query), 300);
  return () => clearTimeout(t);
}, [query]);
```

#### search.tsx
```typescript
// EXACT SAME PATTERN (duplicated code)
useEffect(() => {
  const t = setTimeout(() => setDebouncedQuery(query), 300);
  return () => clearTimeout(t);
}, [query]);
```

#### timeline.tsx
No debouncing (SSE stream)

### ❌ Problems

1. **Code duplication** - same logic in 2 files
2. **Manual cleanup** - easy to get wrong
3. **Not using TanStack ecosystem** - missing `@tanstack/pacer`

### ✅ Better: Use @tanstack/pacer (Not Installed)

**Install**: `npm install @tanstack/pacer`

**Usage**:
```typescript
import { usePacer } from '@tanstack/pacer';

function SearchPage() {
  const [query, setQuery] = useState("");
  const debouncedQuery = usePacer(query, { delay: 300 });
  
  // ... rest of component
}
```

**Benefits**:
- Zero boilerplate
- Built-in cleanup
- Supports throttle, debounce, custom pacers
- Type-safe

### Alternative: Create Custom Hook

If you don't want to add `@tanstack/pacer`:

```typescript
// lib/hooks/useDebounce.ts
export function useDebounce<T>(value: T, delay: number): T {
  const [debounced, setDebounced] = useState(value);
  
  useEffect(() => {
    const t = setTimeout(() => setDebounced(value), delay);
    return () => clearTimeout(t);
  }, [value, delay]);
  
  return debounced;
}
```

---

## 6. Virtualization - @tanstack/react-virtual Unused

### Where It's Needed

#### search.tsx
```typescript
// Current: Renders ALL results (up to 50)
<div className="space-y-4">
  {results.map((thm) => (
    <TheoremCard key={theoremHexId(thm.id)} {...thm} />
  ))}
</div>
```

**Problem**: If 1000+ results, renders 1000 DOM nodes

#### domains/$domain.tsx
```typescript
// Current: Renders up to 50 theorems
<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
  {theorems.map((thm) => <TheoremCard ... />)}
</div>
```

**Problem**: Same - no virtualization for long lists

### ✅ Solution: Use @tanstack/react-virtual

```typescript
import { useVirtualizer } from '@tanstack/react-virtual';

function SearchPage() {
  const parentRef = useRef<HTMLDivElement>(null);
  
  const virtualizer = useVirtualizer({
    count: results.length,
    getScrollElement: () => parentRef.current,
    estimateSize: () => 150, // TheoremCard height estimate
    overscan: 5,
  });
  
  return (
    <div ref={parentRef} style={{ height: '600px', overflow: 'auto' }}>
      <div style={{ height: `${virtualizer.getTotalSize()}px`, position: 'relative' }}>
        {virtualizer.getVirtualItems().map((virtualRow) => {
          const thm = results[virtualRow.index];
          return (
            <div
              key={virtualRow.key}
              style={{
                position: 'absolute',
                top: 0,
                left: 0,
                width: '100%',
                transform: `translateY(${virtualRow.start}px)`,
              }}
            >
              <TheoremCard {...thm} />
            </div>
          );
        })}
      </div>
    </div>
  );
}
```

### Performance Impact

| List Size | Current DOM Nodes | With Virtual | Improvement |
|-----------|------------------|--------------|-------------|
| 50 items  | 50               | ~10          | 5x reduction |
| 500 items | 500              | ~10          | 50x reduction |
| 1000 items| 1000             | ~10          | 100x reduction |

---

## 7. SSE Implementation (Not TanStack, but Relevant)

### lib/sse.ts

```typescript
export function useDiscoveryStream(): DiscoveryEvent[] {
  const [events, setEvents] = useState<DiscoveryEvent[]>([]);
  // ... EventSource logic
}
```

### ✅ What's Good

- Proper cleanup
- Exponential backoff reconnection
- Ring buffer (MAX_EVENTS = 20)

### ⚠️ Potential Enhancement

Consider using **TanStack Query for SSE**:

```typescript
import { useQuery } from '@tanstack/react-query';

export function useDiscoveryStream() {
  return useQuery({
    queryKey: ['sse', 'discoveries'],
    queryFn: () => new Promise(() => {}), // Never resolves
    refetchInterval: false,
    refetchOnWindowFocus: false,
    initialData: [],
    onMount: ({ setData }) => {
      const es = new EventSource('/api/events/discoveries');
      es.addEventListener('discovery', (e) => {
        const event = JSON.parse(e.data);
        setData((prev) => [event, ...prev].slice(0, 20));
      });
      return () => es.close();
    },
  });
}
```

**Benefits**:
- Integrates with Query DevTools
- Can combine with other queries
- Cache invalidation on reconnect

**Trade-offs**:
- Slightly more complex
- Current implementation is fine for simple use case

---

## Optimization Opportunities Summary

| Optimization | Impact | Effort | Priority |
|--------------|--------|--------|----------|
| Use `routerWithQueryClient` | High | Low | 🔴 High |
| Export queryOptions for prefetching | High | Medium | 🔴 High |
| Add route loaders | High | Medium | 🟡 Medium |
| Use `@tanstack/react-virtual` | Medium | Medium | 🟡 Medium |
| Replace manual debounce | Low | Low | 🟢 Low |
| Remove unused packages | Low | Low | 🟢 Low |

---

## Specific Code Changes Needed

### 1. router.tsx

**Current** (lines 1-54):
```typescript
import { QueryClient } from "@tanstack/react-query";
import { createRouter } from "@tanstack/react-router";

export const getRouter = () => {
  const queryClient = getQueryClient();
  const router = createRouter({
    routeTree,
    context: { queryClient },
    scrollRestoration: true,
    defaultPreloadStaleTime: 0,
  });
  return router;
};
```

**Should be**:
```typescript
import { routerWithQueryClient } from "@tanstack/react-router-ssr-query";
import { QueryClient } from "@tanstack/react-query";
import { createRouter } from "@tanstack/react-router";

export const getRouter = () => {
  return routerWithQueryClient(
    createRouter({
      routeTree,
      scrollRestoration: true,
      defaultPreloadStaleTime: 0,
    }),
    makeQueryClient
  );
};
```

### 2. lib/queries.ts

**Add exports** (before hooks):
```typescript
// Export query options for prefetching
export const theoremQueryOptions = (id: string) =>
  queryOptions({
    queryKey: ["theorem", id],
    queryFn: () => apiFetch<ApiTheorem>(`/theorems/${id}`),
    staleTime: 60_000,
    enabled: !!id,
    retry: shouldRetry,
  });

export function useTheorem(id: string) {
  return useQuery(theoremQueryOptions(id));
}

// Repeat for other queries...
```

### 3. routes/index.tsx (lines 24-30)

**Current**:
```typescript
const [query, setQuery] = useState("");
const [debouncedQuery, setDebouncedQuery] = useState("");

useEffect(() => {
  const t = setTimeout(() => setDebouncedQuery(query), 300);
  return () => clearTimeout(t);
}, [query]);
```

**Option A** (add @tanstack/pacer):
```typescript
import { usePacer } from '@tanstack/pacer';

const [query, setQuery] = useState("");
const debouncedQuery = usePacer(query, { delay: 300 });
```

**Option B** (custom hook):
```typescript
const [query, setQuery] = useState("");
const debouncedQuery = useDebounce(query, 300);
```

### 4. routes/search.tsx (line 115+)

**Current**:
```typescript
<div className="space-y-4">
  {results.map((thm) => (
    <TheoremCard key={theoremHexId(thm.id)} {...thm} />
  ))}
</div>
```

**With virtualization**:
```typescript
import { useVirtualizer } from '@tanstack/react-virtual';

// In component:
const parentRef = useRef<HTMLDivElement>(null);
const virtualizer = useVirtualizer({
  count: results.length,
  getScrollElement: () => parentRef.current,
  estimateSize: () => 160,
  overscan: 5,
});

return (
  <div ref={parentRef} className="h-[600px] overflow-auto">
    <div style={{ height: `${virtualizer.getTotalSize()}px`, position: 'relative' }}>
      {virtualizer.getVirtualItems().map((item) => {
        const thm = results[item.index];
        return (
          <div
            key={item.key}
            style={{
              position: 'absolute',
              top: 0,
              left: 0,
              width: '100%',
              transform: `translateY(${item.start}px)`,
            }}
          >
            <TheoremCard {...thm} />
          </div>
        );
      })}
    </div>
  </div>
);
```

### 5. package.json

**Remove these dependencies**:
```diff
-    "@tanstack/react-start": "^1.157.16",
-    "@tanstack/react-store": "^0.8.0",
-    "@tanstack/store": "^0.8.0",
-    "@tanstack/router-plugin": "^1.157.16",
```

**Remove from devDependencies**:
```diff
-    "@tanstack/devtools-vite": "^0.4.1",
```

**Optional: Add pacer**:
```diff
+    "@tanstack/pacer": "^0.2.0",
```

---

## Testing Checklist

After implementing changes:

- [ ] SSR hydration works without double-fetching
- [ ] Search debouncing still works (300ms delay)
- [ ] Virtualized lists scroll smoothly
- [ ] Route prefetching reduces loading states
- [ ] DevTools show query cache correctly
- [ ] No console errors about QueryClient context

---

## Files Requiring Changes

| File | Changes | Lines |
|------|---------|-------|
| `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/package.json` | Remove 5 unused packages | 22-27, 40 |
| `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/router.tsx` | Use routerWithQueryClient | 1-54 |
| `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/routes/__root.tsx` | Verify QueryClientProvider still needed | 67 |
| `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/lib/queries.ts` | Export queryOptions factories | All hooks |
| `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/routes/index.tsx` | Replace manual debounce | 24-30 |
| `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/routes/search.tsx` | Replace manual debounce + add virtualization | 16-22, 90-110 |
| `/Users/nasdin/code/personal/physics-generator/nasrudin-frontend/src/routes/domains/$domain.tsx` | Add virtualization | 64-80 |

---

## Conclusion

The codebase uses TanStack libraries **competently but not optimally**. The main wins:

1. **Remove dead code** - 5 unused packages
2. **Fix SSR integration** - use proper SSR-query utilities
3. **Add virtualization** - huge perf win for long lists
4. **Enable prefetching** - better UX with route loaders
5. **Clean up debouncing** - DRY principle

Estimated effort: **4-6 hours** for full optimization.
