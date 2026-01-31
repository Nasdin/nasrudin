import { QueryClient } from "@tanstack/react-query";
import { createRouter } from "@tanstack/react-router";
import { setupRouterSsrQueryIntegration } from "@tanstack/react-router-ssr-query";
import { RouteError } from "./components/RouteError";
import { RateLimitError } from "./lib/api";

// Import the generated route tree
import { routeTree } from "./routeTree.gen";

function makeQueryClient() {
	return new QueryClient({
		defaultOptions: {
			queries: {
				staleTime: 30_000,
			},
			mutations: {
				onError(error) {
					if (error instanceof RateLimitError) {
						window.dispatchEvent(
							new CustomEvent("ratelimit", { detail: error.retryAfter }),
						);
					}
				},
			},
		},
	});
}

let browserQueryClient: QueryClient | undefined;

function getQueryClient() {
	if (typeof window === "undefined") {
		// SSR: always create a new client
		return makeQueryClient();
	}
	// Browser: reuse the same client
	if (!browserQueryClient) {
		browserQueryClient = makeQueryClient();
	}
	return browserQueryClient;
}

// Create a new router instance
export const getRouter = () => {
	const queryClient = getQueryClient();

	const router = createRouter({
		routeTree,
		context: { queryClient },
		scrollRestoration: true,
		defaultPreloadStaleTime: 0,
		defaultPendingMs: 200,
		defaultPendingMinMs: 300,
		defaultPendingComponent: () => (
			<div className="p-8 max-w-3xl mx-auto">
				<div className="animate-pulse space-y-4">
					<div className="h-6 bg-slate-200 rounded w-1/3" />
					<div className="h-40 bg-slate-100 rounded-xl" />
				</div>
			</div>
		),
		defaultErrorComponent: ({ error, reset }) => (
			<RouteError error={error} reset={reset} />
		),
	});

	// Wire up SSR query integration — handles QueryClientProvider wrapping
	// and dehydration/hydration of query data
	setupRouterSsrQueryIntegration({
		router,
		queryClient,
	});

	return router;
};
