import { infiniteQueryOptions, useInfiniteQuery } from '@tanstack/react-query';
import { createFileRoute } from '@tanstack/react-router';
import { useVirtualizer } from '@tanstack/react-virtual';
import { useEffect, useRef, useState } from 'react';
import { FacetSidebar } from '~/components/browse/FacetSidebar';
import { ResultCard } from '~/components/browse/ResultCard';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { apiFetch } from '~/lib/api';
import { bytesToHex } from '~/lib/hex';
import { useDomains } from '~/lib/queries';
import { useDiscoveryFeed } from '~/lib/sse';
import type { Domain, TheoremListResponse } from '~/lib/types';

const PAGE_SIZE = 50;

/// Cursor-paginated browse list. The server returns 50 theorems per
/// page plus a `next_cursor` (opaque string, encodes
/// `(verified_at_micros, theorem_id)`). Pages stay flat-mapped on the
/// client and an IntersectionObserver-style hook (driven by the
/// virtualizer's last visible index) calls `fetchNextPage()` when the
/// user scrolls within 5 rows of the tail.
const browseInfiniteOptions = (domain: Domain | null) =>
  infiniteQueryOptions({
    queryKey: ['theorems', 'list', domain] as const,
    queryFn: ({ pageParam }) => {
      const cursorParam =
        pageParam == null ? '' : `&cursor=${encodeURIComponent(pageParam as string)}`;
      const url = domain
        ? `/api/theorems?domain=${domain}&limit=${PAGE_SIZE}${cursorParam}`
        : `/api/theorems/recent?limit=${PAGE_SIZE}${cursorParam}`;
      return apiFetch<TheoremListResponse>(url);
    },
    initialPageParam: null as string | null,
    getNextPageParam: (last: TheoremListResponse) => last.next_cursor ?? undefined,
    staleTime: 60_000,
  });

export const Route = createFileRoute('/browse')({
  // Prefetch the first page on hover (defaultPreload: 'intent' fires
  // this when a user hovers a `<Link to="/browse">`). Component reads
  // the same cache via useInfiniteQuery; subsequent pages stream in as
  // the virtualizer reaches the tail.
  loader: async ({ context }) => {
    await context.queryClient.ensureInfiniteQueryData(browseInfiniteOptions(null));
  },
  component: BrowsePage,
});

function BrowsePage() {
  const [domain, setDomain] = useState<Domain | null>(null);
  // Live invalidation: any new pending/verified/rejected theorem refreshes the list.
  useDiscoveryFeed();
  const counts = useDomains();
  const list = useInfiniteQuery(browseInfiniteOptions(domain));

  const parentRef = useRef<HTMLDivElement>(null);
  const theorems = list.data?.pages.flatMap((p) => p.theorems) ?? [];
  // First page carries the capped total — use it for the page-head
  // count even after subsequent pages have loaded.
  const total = list.data?.pages[0]?.total ?? 0;

  const virtualizer = useVirtualizer({
    count: theorems.length,
    getScrollElement: () => parentRef.current,
    estimateSize: () => 120, // Estimated height of each ResultCard
    overscan: 5,
  });

  // When the virtualizer's tail nears the loaded array, fetch the next
  // page. The 5-row prefetch window keeps the user from ever seeing a
  // loading spinner mid-scroll.
  const virtualItems = virtualizer.getVirtualItems();
  const lastVirtualIndex = virtualItems[virtualItems.length - 1]?.index ?? 0;
  useEffect(() => {
    if (
      lastVirtualIndex >= theorems.length - 5 &&
      list.hasNextPage &&
      !list.isFetchingNextPage
    ) {
      list.fetchNextPage();
    }
  }, [lastVirtualIndex, theorems.length, list.hasNextPage, list.isFetchingNextPage, list.fetchNextPage]);

  return (
    <div className="app">
      <AppHeader active="browse" />
      <div className="container-wide" style={{ paddingTop: 24 }}>
        <div
          className="page-head"
          style={{ paddingTop: 24, paddingBottom: 24, borderBottom: 'none' }}
        >
          <span className="overline">The corpus</span>
          <h1>
            Browse{' '}
            <em style={{ fontStyle: 'italic', color: 'var(--terracotta-700)', fontWeight: 300 }}>
              {total.toLocaleString()}
            </em>{' '}
            verified theorems
          </h1>
          <p className="lede">
            Click any result to see its full Lean 4 proof, lineage, and downstream uses.
          </p>
        </div>
        <div className="page-body" style={{ paddingTop: 16 }}>
          <div className="search-layout">
            <FacetSidebar counts={counts.data ?? {}} active={domain} onChange={setDomain} />
            <div>
              <div className="search-results-bar">
                <span>
                  <strong>{theorems.length.toLocaleString()}</strong> loaded
                  {list.hasNextPage ? ` of ${total.toLocaleString()}` : ''}
                  {list.isFetchingNextPage && ' · fetching more…'}
                </span>
              </div>
              {list.isPending && <p style={{ color: 'var(--ink-500)' }}>loading…</p>}
              {!list.isPending && theorems.length > 0 && (
                <div
                  ref={parentRef}
                  style={{
                    height: 'calc(100vh - 300px)',
                    overflow: 'auto',
                  }}
                >
                  <div
                    style={{
                      height: `${virtualizer.getTotalSize()}px`,
                      width: '100%',
                      position: 'relative',
                    }}
                  >
                    {virtualizer.getVirtualItems().map((virtualItem) => {
                      const theorem = theorems[virtualItem.index];
                      if (!theorem) return null;
                      return (
                        <div
                          key={bytesToHex(theorem.id)}
                          style={{
                            position: 'absolute',
                            top: 0,
                            left: 0,
                            width: '100%',
                            transform: `translateY(${virtualItem.start}px)`,
                          }}
                        >
                          <ResultCard thm={theorem} />
                        </div>
                      );
                    })}
                  </div>
                </div>
              )}
            </div>
          </div>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}
