/// <reference types="vite/client" />

import { useQueryClient } from '@tanstack/react-query';
import { useEffect, useRef, useState } from 'react';
import { API_BASE } from './api';
import type { ConjectureSseEvent } from './types';

/**
 * Subscribes to the /api/events/discoveries SSE stream and invalidates
 * the React Query cache for theorem-related queries on each event.
 */
export function useDiscoveryFeed(onEvent?: (e: MessageEvent) => void) {
  const qc = useQueryClient();
  const ref = useRef<EventSource | null>(null);

  useEffect(() => {
    if (typeof window === 'undefined') return; // SSR guard
    const es = new EventSource(`${API_BASE}/api/events/discoveries`);

    const handler = (event: MessageEvent) => {
      qc.invalidateQueries({ queryKey: ['theorems'] });
      qc.invalidateQueries({ queryKey: ['workers'] });
      onEvent?.(event);
    };

    for (const name of [
      'theorem_pending',
      'theorem_verified',
      'theorem_rejected',
      'ga_discovery',
    ]) {
      es.addEventListener(name, handler);
    }

    es.onerror = () => {
      // Browser auto-reconnects; nothing to do here.
    };

    ref.current = es;
    return () => {
      es.close();
      ref.current = null;
    };
  }, [qc, onEvent]);
}

/**
 * Subscribes to the /api/events/stats SSE stream for GA tick + worker heartbeat
 * events. Returns the latest event via the optional callback.
 */
export function useStatsStream(onEvent?: (e: MessageEvent) => void) {
  const ref = useRef<EventSource | null>(null);

  useEffect(() => {
    if (typeof window === 'undefined') return;
    const es = new EventSource(`${API_BASE}/api/events/stats`);

    const handler = (event: MessageEvent) => {
      onEvent?.(event);
    };

    for (const name of ['ga_status_tick', 'worker_heartbeat']) {
      es.addEventListener(name, handler);
    }

    es.onerror = () => {};

    ref.current = es;
    return () => {
      es.close();
      ref.current = null;
    };
  }, [onEvent]);
}

/**
 * Subscribes to the per-job /api/conjecture/{id}/sse stream and accumulates
 * events into a list. Returns the full ordered event log; the server replays
 * history on connect and then streams live changes.
 */
export function useConjectureStream(id: string | null): ConjectureSseEvent[] {
  const [events, setEvents] = useState<ConjectureSseEvent[]>([]);

  useEffect(() => {
    if (!id) return;
    if (typeof window === 'undefined') return;
    setEvents([]);
    const es = new EventSource(`${API_BASE}/api/conjecture/${id}/sse`, {
      withCredentials: true,
    });

    const handler = (e: MessageEvent) => {
      try {
        const parsed = JSON.parse(e.data) as ConjectureSseEvent;
        setEvents((prev) => [...prev, parsed]);
      } catch {
        // Silently drop malformed payloads — keep-alive pings ride the
        // event:"ping" channel which we don't subscribe to.
      }
    };

    for (const kind of ['state_change', 'progress', 'candidate_verified', 'complete']) {
      es.addEventListener(kind, handler);
    }
    es.onerror = () => {};

    return () => es.close();
  }, [id]);

  return events;
}
