// TypeScript types matching the Rust backend JSON serialization.
// See: engine/crates/core/src/theorem.rs, engine/crates/rocks/src/lib.rs,
//      engine/crates/ga/src/engine.rs

/** TheoremId is [u8; 8] in Rust — serialized as a JSON array of numbers. */
export type TheoremId = number[];

/** Matches engine/crates/core/src/theorem.rs FitnessScore */
export interface FitnessScore {
	novelty: number;
	complexity: number;
	depth: number;
	dimensional: number;
	symmetry: number;
	connectivity: number;
	nasrudin_relevance: number;
}

/** Matches engine/crates/core/src/theorem.rs VerificationStatus (serde enum) */
export type VerificationStatus =
	| "Pending"
	| "Timeout"
	| { Verified: { proof_term: number[]; tactic_used: string } }
	| { Rejected: { reason: string } };

/** Matches engine/crates/core/src/theorem.rs TheoremOrigin (serde enum) */
export type TheoremOrigin =
	| "Axiom"
	| { Crossover: { parent_a: TheoremId; parent_b: TheoremId } }
	| { Mutation: { parent: TheoremId; operator: string } }
	| { Simplification: { parent: TheoremId } }
	| { Imported: { source: string } }
	| { DomainTransfer: { parent: TheoremId; from: string; to: string } };

/** Matches engine/crates/core/src/theorem.rs Theorem */
export interface ApiTheorem {
	id: TheoremId;
	statement: unknown; // Expr AST — opaque on the frontend
	canonical: string;
	latex: string;
	proof: unknown; // ProofTree — opaque for now
	depth: number;
	complexity: number;
	domain: string; // Serde serializes Domain enum variants as strings
	dimension: unknown | null;
	parents: TheoremId[];
	children: TheoremId[];
	verified: VerificationStatus;
	fitness: FitnessScore;
	generation: number;
	created_at: number; // unix epoch seconds
	origin: TheoremOrigin;
}

/** Matches engine/crates/rocks/src/lib.rs DbStats */
export interface DbStats {
	total_theorems: number;
	total_verified: number;
	total_rejected: number;
	total_pending: number;
	total_axioms: number;
	max_depth: number;
	max_generation: number;
	domain_counts: Record<string, number>;
}

/** Matches engine/crates/ga/src/engine.rs GaStatusSnapshot */
export interface GaStatus {
	total_generations: number;
	total_population: number;
	num_islands: number;
	candidates_sent: number;
	verified_discoveries: number;
	running: boolean;
}

/** Matches engine/crates/ga/src/engine.rs DiscoveryEvent */
export interface DiscoveryEvent {
	theorem_id: string; // hex-encoded
	canonical: string;
	latex: string;
	domain: string;
	depth: number;
	generation: number;
	fitness: FitnessScore;
	timestamp: number;
}

/** Search endpoint response shape from /api/theorems */
export interface SearchResponse {
	theorems: ApiTheorem[];
	total: number;
	error?: string;
}

/** Lineage record from /api/theorems/{id}/lineage */
export interface LineageRecord {
	theorem_id: TheoremId;
	parents: TheoremId[];
	children: TheoremId[];
	axiom_ancestors: TheoremId[];
}

/** Axiom from /api/axioms */
export interface ApiAxiom {
	name: string;
	domain: string;
	description: string;
}

/** Response from /api/axioms */
export interface AxiomsResponse {
	axioms: ApiAxiom[];
	total: number;
}

/** Health check response from /api/health */
export interface HealthResponse {
	status: string;
	version: string;
}
