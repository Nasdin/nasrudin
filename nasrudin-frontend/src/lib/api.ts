import type { FitnessScore, TheoremOrigin, VerificationStatus } from "./types";

const API_BASE = "/api";

export class RateLimitError extends Error {
	retryAfter: number;
	constructor(retryAfter: number) {
		super(`Rate limited. Retry after ${retryAfter}s`);
		this.name = "RateLimitError";
		this.retryAfter = retryAfter;
	}
}

export async function apiFetch<T>(
	path: string,
	init?: RequestInit,
): Promise<T> {
	const res = await fetch(`${API_BASE}${path}`, {
		credentials: "include",
		...init,
	});

	if (res.status === 429) {
		const retryAfter = Number.parseInt(
			res.headers.get("retry-after") ?? "5",
			10,
		);
		throw new RateLimitError(retryAfter);
	}

	if (!res.ok) {
		const body = await res.json().catch(() => ({}));
		throw new Error(
			(body as { error?: string }).error ?? `API error: ${res.status}`,
		);
	}

	return res.json();
}

// ---------------------------------------------------------------------------
// Utility functions
// ---------------------------------------------------------------------------

/** Convert a [u8; 8] array to a hex string ID. */
export function theoremHexId(id: number[]): string {
	return id.map((b) => b.toString(16).padStart(2, "0")).join("");
}

/** Convert PascalCase/snake_case domain enum variant to display string. */
export function domainDisplay(domain: string): string {
	const map: Record<string, string> = {
		PureMath: "Pure Math",
		ClassicalMechanics: "Classical Mechanics",
		Electromagnetism: "Electromagnetism",
		SpecialRelativity: "Special Relativity",
		GeneralRelativity: "General Relativity",
		QuantumMechanics: "Quantum Mechanics",
		QuantumFieldTheory: "Quantum Field Theory",
		StatisticalMechanics: "Statistical Mechanics",
		Thermodynamics: "Thermodynamics",
		Optics: "Optics",
		FluidDynamics: "Fluid Dynamics",
	};
	return map[domain] ?? domain.replace(/([A-Z])/g, " $1").trim();
}

/** Average of all 7 fitness scores. */
export function totalFitness(f: FitnessScore): number {
	return (
		(f.novelty +
			f.complexity +
			f.depth +
			f.dimensional +
			f.symmetry +
			f.connectivity +
			f.nasrudin_relevance) /
		7
	);
}

/** Check if a VerificationStatus is Verified. */
export function isVerified(v: VerificationStatus): boolean {
	return typeof v === "object" && v !== null && "Verified" in v;
}

/** Extract a human-readable operator name from TheoremOrigin. */
export function originOperator(o: TheoremOrigin): string {
	if (o === "Axiom") return "Axiom";
	if (typeof o === "object") {
		if ("Crossover" in o) return "Crossover";
		if ("Mutation" in o) return `Mutation (${o.Mutation.operator})`;
		if ("Simplification" in o) return "Simplification";
		if ("Imported" in o) return `Import (${o.Imported.source})`;
		if ("DomainTransfer" in o) return "Domain Transfer";
	}
	return "Unknown";
}

/** Convert unix epoch seconds to an ISO timestamp string. */
export function epochToIso(epoch: number): string {
	return new Date(epoch * 1000).toISOString();
}
