import { useEffect, useState } from "react";

/**
 * Global rate-limit toast. Subscribe to the custom "ratelimit" event
 * dispatched by the QueryClient's onError callback.
 */
export default function RateLimitToast() {
	const [retryAfter, setRetryAfter] = useState<number | null>(null);

	useEffect(() => {
		function onRateLimit(e: Event) {
			const seconds = (e as CustomEvent<number>).detail;
			setRetryAfter(seconds);
		}
		window.addEventListener("ratelimit", onRateLimit);
		return () => window.removeEventListener("ratelimit", onRateLimit);
	}, []);

	// Countdown timer
	useEffect(() => {
		if (retryAfter == null) return;
		if (retryAfter <= 0) {
			setRetryAfter(null);
			return;
		}
		const t = setTimeout(
			() => setRetryAfter((s) => (s != null ? s - 1 : null)),
			1000,
		);
		return () => clearTimeout(t);
	}, [retryAfter]);

	if (retryAfter == null) return null;

	return (
		<div className="fixed bottom-4 right-4 z-50 rounded-lg border border-amber-300 bg-amber-50 px-4 py-3 text-sm text-amber-800 shadow-lg">
			<p className="font-medium">Slow down</p>
			<p className="text-amber-600">Retry in {retryAfter}s</p>
		</div>
	);
}
