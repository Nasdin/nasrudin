import { createServerFn } from "@tanstack/react-start";

const API_BASE = "http://localhost:3001/api";

async function apiFetchServer<T>(path: string): Promise<T> {
	const res = await fetch(`${API_BASE}${path}`);
	if (!res.ok) {
		const body = await res.json().catch(() => ({}));
		throw new Error(
			(body as { error?: string }).error ?? `API error: ${res.status}`,
		);
	}
	return res.json();
}

export const fetchStats = createServerFn({ method: "GET" }).handler(async () =>
	apiFetchServer("/stats"),
);

export const fetchGaStatus = createServerFn({ method: "GET" }).handler(
	async () => apiFetchServer("/ga/status"),
);

export const fetchHealth = createServerFn({ method: "GET" }).handler(
	async () => apiFetchServer("/health"),
);

export const fetchTheorem = createServerFn({ method: "GET" })
	.inputValidator((input: { id: string }) => input)
	.handler(async ({ data }) => apiFetchServer(`/theorems/${data.id}`));

export const fetchSearchTheorems = createServerFn({ method: "GET" })
	.inputValidator((input: { queryString: string }) => input)
	.handler(async ({ data }) => {
		const qs = data.queryString;
		return apiFetchServer(`/theorems${qs ? `?${qs}` : ""}`);
	});

export const fetchRecentTheorems = createServerFn({ method: "GET" })
	.inputValidator((input: { limit: number }) => input)
	.handler(async ({ data }) =>
		apiFetchServer(`/theorems/recent?limit=${data.limit}`),
	);

export const fetchLineage = createServerFn({ method: "GET" })
	.inputValidator((input: { id: string }) => input)
	.handler(async ({ data }) =>
		apiFetchServer(`/theorems/${data.id}/lineage`),
	);

export const fetchProof = createServerFn({ method: "GET" })
	.inputValidator((input: { id: string }) => input)
	.handler(async ({ data }) =>
		apiFetchServer(`/theorems/${data.id}/proof`),
	);

export const fetchDomains = createServerFn({ method: "GET" }).handler(
	async () => apiFetchServer("/domains"),
);
