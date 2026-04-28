import { useQuery } from '@tanstack/react-query';
import { createFileRoute } from '@tanstack/react-router';
import { useState } from 'react';
import { FacetSidebar } from '~/components/browse/FacetSidebar';
import { ResultCard } from '~/components/browse/ResultCard';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { apiFetch } from '~/lib/api';
import { useDomains } from '~/lib/queries';
import { useDiscoveryFeed } from '~/lib/sse';
import type { Domain, Theorem } from '~/lib/types';

export const Route = createFileRoute('/browse')({ component: BrowsePage });

function BrowsePage() {
  const [domain, setDomain] = useState<Domain | null>(null);
  // Live invalidation: any new pending/verified/rejected theorem refreshes the list.
  useDiscoveryFeed();
  const counts = useDomains();
  const list = useQuery({
    queryKey: ['theorems', 'list', domain],
    queryFn: () =>
      apiFetch<{ theorems: Theorem[]; total: number }>(
        domain ? `/api/theorems?domain=${domain}&limit=50` : `/api/theorems/recent?limit=50`,
      ),
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
              {list.data?.theorems.map((t) => (
                <ResultCard key={t.id} thm={t} />
              ))}
            </div>
          </div>
        </div>
      </div>
      <AppFooter />
    </div>
  );
}
