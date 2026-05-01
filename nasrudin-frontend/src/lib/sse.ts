/// <reference types="vite/client" />

import { useQueryClient } from '@tanstack/react-query';
import { useEffect, useRef, useState } from 'react';
import { API_BASE } from './api';
import type { ConjectureSseEvent, ResearchJobEvent } from './types';

/**
 * Subscribes to the /api/events/discoveries SSE stream and invalidates
 * the React Query cache for theorem-related queries on each event.
 *
 * Invalidations are debounced to a 250 ms window so a verification burst
 * doesn't trigger 100 invalidations/sec across every mounted query
 * consumer. Reconnection on transient errors uses exponential backoff
 * (1 s → 30 s) instead of the browser's default — when the API restarts,
 * thousands of clients reconnecting in lockstep is a thundering herd.
 */
export function useDiscoveryFeed(onEvent?: (e: MessageEvent) => void) {
  const qc = useQueryClient();
  const ref = useRef<EventSource | null>(null);

  useEffect(() => {
    if (typeof window === 'undefined') return; // SSR guard

    let closed = false;
    let backoffMs = 1000;
    const maxBackoffMs = 30000;
    let pendingInvalidate: number | null = null;
    let pendingFlags = { theorems: false, workers: false, stats: false };

    const flushInvalidations = () => {
      pendingInvalidate = null;
      const flags = pendingFlags;
      pendingFlags = { theorems: false, workers: false, stats: false };
      if (flags.theorems) qc.invalidateQueries({ queryKey: ['theorems'] });
      if (flags.workers) qc.invalidateQueries({ queryKey: ['workers'] });
      if (flags.stats) qc.invalidateQueries({ queryKey: ['stats', 'landing'] });
    };

    const scheduleFlush = () => {
      if (pendingInvalidate !== null) return;
      pendingInvalidate = window.setTimeout(flushInvalidations, 250);
    };

    const connect = () => {
      if (closed) return;
      const es = new EventSource(`${API_BASE}/api/events/discoveries`);
      ref.current = es;

      const handler = (event: MessageEvent) => {
        // Theorem events refresh the funnel + the recent feed but do NOT
        // affect the worker list — that's heartbeat-driven on a different
        // SSE channel, so don't blow that cache.
        pendingFlags.theorems = true;
        pendingFlags.stats = true;
        scheduleFlush();
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

      es.onopen = () => {
        backoffMs = 1000; // success — reset
      };

      es.onerror = () => {
        es.close();
        ref.current = null;
        if (closed) return;
        const wait = backoffMs;
        backoffMs = Math.min(backoffMs * 2, maxBackoffMs);
        window.setTimeout(connect, wait);
      };
    };

    connect();
    return () => {
      closed = true;
      if (pendingInvalidate !== null) window.clearTimeout(pendingInvalidate);
      ref.current?.close();
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

/**
 * Subscribe to a paid Researcher job's `/api/research/jobs/{id}/events`
 * SSE stream. Events arrive as `JobEvent` JSON; we accumulate them in
 * order and return the live list. Handles all five event kinds emitted
 * by the server: `job_state`, `progress`, `theorem_verified`, `proved`,
 * `budget_exhausted`, `cancelled`.
 */
export function useResearchJobStream(id: string | null): ResearchJobEvent[] {
  const [events, setEvents] = useState<ResearchJobEvent[]>([]);

  useEffect(() => {
    if (!id) return;
    if (typeof window === 'undefined') return;
    setEvents([]);
    const es = new EventSource(`${API_BASE}/api/research/jobs/${id}/events`, {
      withCredentials: true,
    });

    es.onmessage = (e: MessageEvent) => {
      try {
        const parsed = JSON.parse(e.data) as ResearchJobEvent;
        setEvents((prev) => [...prev, parsed]);
      } catch {
        // Malformed payloads / keep-alives — drop silently.
      }
    };
    es.onerror = () => {
      // EventSource auto-reconnects on transient network errors;
      // the user keeps seeing the accumulated history.
    };

    return () => es.close();
  }, [id]);

  return events;
}
