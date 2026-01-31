import { queryOptions, useQuery } from "@tanstack/react-query";
import { RateLimitError } from "./api";
import {
	fetchDomains,
	fetchGaStatus,
	fetchHealth,
	fetchLineage,
	fetchProof,
	fetchRecentTheorems,
	fetchSearchTheorems,
	fetchStats,
	fetchTheorem,
} from "./server-fns";
import type {
	ApiTheorem,
	DbStats,
	GaStatus,
	HealthResponse,
	LineageRecord,
	SearchResponse,
} from "./types";

// ---------------------------------------------------------------------------
// Shared retry logic: never retry on 429 (rate limit)
// ---------------------------------------------------------------------------

function shouldRetry(failureCount: number, error: Error): boolean {
	if (error instanceof RateLimitError) return false;
	return failureCount < 3;
}

// ---------------------------------------------------------------------------
// Query option factories — exported so loaders can call ensureQueryData()
// ---------------------------------------------------------------------------

export const healthQueryOptions = () =>
	queryOptions({
		queryKey: ["health"],
		queryFn: () => fetchHealth() as Promise<HealthResponse>,
		staleTime: 30_000,
		retry: shouldRetry,
	});

export const statsQueryOptions = () =>
	queryOptions({
		queryKey: ["stats"],
		queryFn: () => fetchStats() as Promise<DbStats>,
		staleTime: 30_000,
		refetchOnWindowFocus: true,
		retry: shouldRetry,
	});

export const gaStatusQueryOptions = () =>
	queryOptions({
		queryKey: ["ga-status"],
		queryFn: () => fetchGaStatus() as Promise<GaStatus>,
		staleTime: 30_000,
		refetchOnWindowFocus: true,
		retry: shouldRetry,
	});

export const theoremQueryOptions = (id: string) =>
	queryOptions({
		queryKey: ["theorem", id],
		queryFn: () => fetchTheorem({ data: { id } }) as Promise<ApiTheorem>,
		staleTime: 60_000,
		enabled: !!id,
		retry: shouldRetry,
	});

export interface SearchParams {
	domain?: string;
	depth?: number;
	generation?: number;
	latex?: string;
	axiom?: string;
	verified?: boolean;
	limit?: number;
}

function buildSearchQueryString(params: SearchParams): string {
	const searchParams = new URLSearchParams();
	if (params.domain) searchParams.set("domain", params.domain);
	if (params.depth != null) searchParams.set("depth", String(params.depth));
	if (params.generation != null)
		searchParams.set("generation", String(params.generation));
	if (params.latex) searchParams.set("latex", params.latex);
	if (params.axiom) searchParams.set("axiom", params.axiom);
	if (params.verified != null)
		searchParams.set("verified", String(params.verified));
	if (params.limit != null) searchParams.set("limit", String(params.limit));
	return searchParams.toString();
}

export const searchTheoremsQueryOptions = (params: SearchParams) => {
	const qs = buildSearchQueryString(params);
	return queryOptions({
		queryKey: ["search-theorems", params],
		queryFn: () =>
			fetchSearchTheorems({
				data: { queryString: qs },
			}) as Promise<SearchResponse>,
		staleTime: 60_000,
		retry: shouldRetry,
	});
};

export const recentTheoremsQueryOptions = (limit = 20) =>
	queryOptions({
		queryKey: ["recent-theorems", limit],
		queryFn: () =>
			fetchRecentTheorems({ data: { limit } }) as Promise<SearchResponse>,
		staleTime: 30_000,
		retry: shouldRetry,
	});

export const lineageQueryOptions = (id: string) =>
	queryOptions({
		queryKey: ["lineage", id],
		queryFn: () =>
			fetchLineage({ data: { id } }) as Promise<LineageRecord>,
		staleTime: 60_000,
		enabled: !!id,
		retry: shouldRetry,
	});

export const proofQueryOptions = (id: string) =>
	queryOptions({
		queryKey: ["proof", id],
		queryFn: () => fetchProof({ data: { id } }) as Promise<unknown>,
		staleTime: 60_000,
		enabled: !!id,
		retry: shouldRetry,
	});

export const domainsQueryOptions = () =>
	queryOptions({
		queryKey: ["domains"],
		queryFn: () => fetchDomains() as Promise<Record<string, number>>,
		staleTime: 5 * 60_000,
		retry: shouldRetry,
	});

// ---------------------------------------------------------------------------
// Convenience hooks — thin wrappers around the option factories
// ---------------------------------------------------------------------------

export function useHealth() {
	return useQuery(healthQueryOptions());
}

export function useStats() {
	return useQuery(statsQueryOptions());
}

export function useGaStatus() {
	return useQuery(gaStatusQueryOptions());
}

export function useTheorem(id: string) {
	return useQuery(theoremQueryOptions(id));
}

export function useSearchTheorems(params: SearchParams) {
	return useQuery(searchTheoremsQueryOptions(params));
}

export function useRecentTheorems(limit = 20) {
	return useQuery(recentTheoremsQueryOptions(limit));
}

export function useLineage(id: string) {
	return useQuery(lineageQueryOptions(id));
}

export function useProof(id: string) {
	return useQuery(proofQueryOptions(id));
}

export function useDomains() {
	return useQuery(domainsQueryOptions());
}
