import { memo, useEffect, useState } from 'react';
import { useLandingStats } from '~/lib/queries';
import { useDiscoveryFeed } from '~/lib/sse';

function formatAgo(iso: string | null): string | null {
  if (!iso) return null;
  const t = Date.parse(iso);
  if (!Number.isFinite(t)) return null;
  const seconds = Math.max(0, Math.floor((Date.now() - t) / 1000));
  if (seconds < 60) return `${seconds}s ago`;
  const minutes = Math.floor(seconds / 60);
  if (minutes < 60) return `${minutes}m ago`;
  const hours = Math.floor(minutes / 60);
  if (hours < 24) return `${hours}h ago`;
  const days = Math.floor(hours / 24);
  return `${days}d ago`;
}

function prettyDomain(d: string): string {
  return d.replace(/_/g, ' ');
}

export const PulseStrip = memo(function PulseStrip() {
  const stats = useLandingStats();
  useDiscoveryFeed();

  const [, tick] = useState(0);
  useEffect(() => {
    const id = window.setInterval(() => tick((n) => n + 1), 1000);
    return () => window.clearInterval(id);
  }, []);

  const data = stats.data;
  const ago = data ? formatAgo(data.last_verified_at) : null;

  return (
    <div className="pulse-strip" aria-live="polite">
      <span className="pulse-dot" aria-hidden="true" />
      <span className="pulse-stat">
        <strong>{data?.active_workers ?? '—'}</strong>{' '}
        worker{data?.active_workers === 1 ? '' : 's'} online
      </span>
      <span className="pulse-sep">·</span>
      <span className="pulse-stat">
        <strong>{data?.verified_24h?.toLocaleString() ?? '—'}</strong> verified in 24h
      </span>
      {ago && data?.last_verified_domain && (
        <>
          <span className="pulse-sep">·</span>
          <span className="pulse-stat">
            last verified <strong>{ago}</strong> in{' '}
            <code className="pulse-domain">{prettyDomain(data.last_verified_domain)}</code>
          </span>
        </>
      )}
    </div>
  );
});
