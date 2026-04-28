export type Domain =
  | 'PureMath'
  | 'ClassicalMechanics'
  | 'Electromagnetism'
  | 'SpecialRelativity'
  | 'GeneralRelativity'
  | 'QuantumMechanics'
  | 'QuantumFieldTheory'
  | 'StatisticalMechanics'
  | 'Thermodynamics'
  | 'Optics'
  | 'FluidDynamics';

/**
 * Theorem row as returned by the Phase 9 read endpoints
 * (`GET /api/theorems`, `…/recent`, `…/{id}`).
 *
 * Field set + names mirror SeaORM's `theorems::Model`
 * (`engine/crates/pg/src/entity/theorems.rs`). `BYTEA` columns serialize as
 * JSON arrays of byte numbers (`Vec<u8>` → `[1,2,3,4,5,6,7,8]`), NOT hex
 * strings — use `bytesToHex` from `./hex` when displaying or routing on
 * `id` / `canonical_hash` / `parents`.
 */
export interface Theorem {
  /** 8-byte primary key, BYTEA serialized as array of byte numbers. */
  id: number[];
  /** 8-byte canonical hash (unique), BYTEA serialized as array of byte numbers. */
  canonical_hash: number[];
  canonical_statement: string;
  latex: string | null;
  lean_source: string;
  /** `Domain` enum stringified. The DB column is plain TEXT so any string is structurally valid. */
  domain: string;
  axioms_used: string[];
  /** `serde_json::Value` — kept opaque; the chain shape is engine-internal. */
  chain_json: unknown;
  /** Each parent is an 8-byte BYTEA, also serialized as a byte-array. */
  parents: number[][] | null;
  origin_kind: string;
  origin_payload: unknown | null;
  depth: number | null;
  complexity: number | null;
  generation: number | null;
  fitness_novelty: number | null;
  fitness_compactness: number | null;
  fitness_dimensional_correctness: number | null;
  fitness_domain_coverage: number | null;
  fitness_axiom_efficiency: number | null;
  fitness_nasrudin_relevance: number | null;
  fitness_depth_score: number | null;
  dimension: number[] | null;
  engine_git_sha: string;
  lean_version: string;
  verification_tactic: string | null;
  verification_duration_ms: number | null;
  verification_path: 'A' | 'B' | string | null;
  status: 'Pending' | 'Verified' | 'Rejected' | string;
  rejected_reason: string | null;
  contributor_id: string;
  /** ISO 8601 timestamp with offset (`DateTimeWithTimeZone`). */
  created_at: string;
  /** ISO 8601 timestamp with offset, or `null` while pending. */
  verified_at: string | null;
}

/** Response shape of `GET /api/theorems` and `GET /api/theorems/recent`. */
export interface TheoremListResponse {
  theorems: Theorem[];
  next_cursor: string | null;
  total: number;
  total_capped: boolean;
}

export interface AuthUser {
  id: string;
  email: string;
  display_name: string | null;
  created_at: string;
}

export type ApiKeyKind = 'live' | 'worker';

export interface ApiKeySummary {
  id: string;
  name: string;
  kind: ApiKeyKind;
  prefix: string;
  last_used_at: string | null;
  created_at: string;
  expires_at: string | null;
}

export interface NewApiKey extends ApiKeySummary {
  full_key: string;
}

export interface SavedSearch {
  id: string;
  user_id: string;
  latex: string;
  label: string | null;
  created_at: string;
}

export interface WorkerOwner {
  user_id: string;
  display_name: string | null;
  /** Local part of the email — a short public handle. */
  handle: string;
}

export interface Worker {
  id: string;
  name: string | null;
  host: string | null;
  last_seen: string;
  theorems_contributed: number;
  status: 'Active' | 'Inactive' | 'Disconnected' | 'active' | 'inactive' | 'disconnected';
  last_heartbeat_at?: string | null;
  last_contribution_at?: string | null;
  current_generation?: number;
  theorems_produced_total?: number;
  uptime_seconds?: number;
  engine_git_sha?: string | null;
  /** Present only on the public list when the worker's api-key is linked to a user. */
  owner?: WorkerOwner | null;
}

export interface MeStats {
  saved_searches: number;
  api_keys: number;
  theorems_total?: number;
  theorems_recent?: Theorem[];
}

export interface UserProfileFields {
  bio?: string;
  handle?: string;
  institution?: string;
  field?: string;
  location?: string;
  website?: string;
}

export interface MeProfile {
  display_name: string | null;
  email: string;
  profile: UserProfileFields;
}
