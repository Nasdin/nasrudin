import { useQuery } from '@tanstack/react-query';
import { createFileRoute } from '@tanstack/react-router';
import { useVirtualizer } from '@tanstack/react-virtual';
import { useRef, useState } from 'react';
import { FacetSidebar } from '~/components/browse/FacetSidebar';
import { ResultCard } from '~/components/browse/ResultCard';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { apiFetch } from '~/lib/api';
import { bytesToHex } from '~/lib/hex';
import { useDomains } from '~/lib/queries';
import { useDiscoveryFeed } from '~/lib/sse';
import type { Domain, TheoremListResponse } from '~/lib/types';

export const Route = createFileRoute('/browse')({ component: BrowsePage });

function BrowsePage() {
  const [domain, setDomain] = useState<Domain | null>(null);
  // Live invalidation: any new pending/verified/rejected theorem refreshes the list.
  useDiscoveryFeed();
  const counts = useDomains();
  const list = useQuery({
    queryKey: ['theorems', 'list', domain],
    queryFn: () =>
      apiFetch<TheoremListResponse>(
        domain ? `/api/theorems?domain=${domain}&limit=50` : `/api/theorems/recent?limit=50`,
      ),
  });

  const parentRef = useRef<HTMLDivElement>(null);
  const theorems = list.data?.theorems ?? [];

  const virtualizer = useVirtualizer({
    count: theorems.length,
    getScrollElement: () => parentRef.current,
    estimateSize: () => 120, // Estimated height of each ResultCard
    overscan: 5,
  });

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
              {(list.data?.total ?? 0).toLocaleString()}
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
                  <strong>{(list.data?.theorems.length ?? 0).toLocaleString()}</strong> results
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
