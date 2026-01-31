import { useEffect, useRef, useState } from "react";
import { engineUIStore } from "./stores";
import type { DiscoveryEvent, GaStatus } from "./types";

const SSE_URL = "/api/events/discoveries";
const STATS_SSE_URL = "/api/events/stats";
const MAX_EVENTS = 20;
const INITIAL_RECONNECT_MS = 1000;
const MAX_RECONNECT_MS = 30_000;

/**
 * SSE hook for live discovery events.
 * Maintains a ring buffer of the last 20 events, newest first.
 * Reconnects on error with exponential backoff.
 * Updates engineUIStore with streaming state.
 */
export function useDiscoveryStream(): DiscoveryEvent[] {
	const [events, setEvents] = useState<DiscoveryEvent[]>([]);
	const reconnectDelay = useRef(INITIAL_RECONNECT_MS);

	useEffect(() => {
		let es: EventSource | null = null;
		let timeout: ReturnType<typeof setTimeout> | null = null;
		let cancelled = false;

		function connect() {
			if (cancelled) return;

			es = new EventSource(SSE_URL);

			es.addEventListener("discovery", (e: MessageEvent) => {
				try {
					const event: DiscoveryEvent = JSON.parse(e.data);
					setEvents((prev) => [event, ...prev].slice(0, MAX_EVENTS));
					// Reset backoff on successful message
					reconnectDelay.current = INITIAL_RECONNECT_MS;
					// Update engine UI store
					engineUIStore.setState((prev) => ({
						...prev,
						isStreaming: true,
						lastEventTimestamp: Date.now(),
						eventCount: prev.eventCount + 1,
					}));
				} catch {
					// Ignore malformed events
				}
			});

			es.addEventListener("open", () => {
				reconnectDelay.current = INITIAL_RECONNECT_MS;
				engineUIStore.setState((prev) => ({
					...prev,
					isStreaming: true,
				}));
			});

			es.addEventListener("error", () => {
				es?.close();
				engineUIStore.setState((prev) => ({
					...prev,
					isStreaming: false,
				}));
				if (cancelled) return;
				// Exponential backoff
				const delay = reconnectDelay.current;
				reconnectDelay.current = Math.min(delay * 2, MAX_RECONNECT_MS);
				timeout = setTimeout(connect, delay);
			});
		}

		connect();

		return () => {
			cancelled = true;
			es?.close();
			if (timeout) clearTimeout(timeout);
			engineUIStore.setState((prev) => ({
				...prev,
				isStreaming: false,
			}));
		};
	}, []);

	return events;
}

/**
 * SSE hook for live GA engine stats.
 * Receives GaStatus snapshots every 5 seconds from the server.
 * Reconnects on error with exponential backoff.
 */
export function useStatsStream(): GaStatus | null {
	const [status, setStatus] = useState<GaStatus | null>(null);
	const reconnectDelay = useRef(INITIAL_RECONNECT_MS);

	useEffect(() => {
		let es: EventSource | null = null;
		let timeout: ReturnType<typeof setTimeout> | null = null;
		let cancelled = false;

		function connect() {
			if (cancelled) return;

			es = new EventSource(STATS_SSE_URL);

			es.addEventListener("stats", (e: MessageEvent) => {
				try {
					const data: GaStatus = JSON.parse(e.data);
					setStatus(data);
					reconnectDelay.current = INITIAL_RECONNECT_MS;
				} catch {
					// Ignore malformed events
				}
			});

			es.addEventListener("open", () => {
				reconnectDelay.current = INITIAL_RECONNECT_MS;
			});

			es.addEventListener("error", () => {
				es?.close();
				if (cancelled) return;
				const delay = reconnectDelay.current;
				reconnectDelay.current = Math.min(delay * 2, MAX_RECONNECT_MS);
				timeout = setTimeout(connect, delay);
			});
		}

		connect();

		return () => {
			cancelled = true;
			es?.close();
			if (timeout) clearTimeout(timeout);
		};
	}, []);

	return status;
}
