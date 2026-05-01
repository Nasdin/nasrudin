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
  /** Email of the user who owns the worker that contributed this theorem. */
  user_email: string | null;
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

/** Database statistics from `GET /api/stats`. */
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

export interface LandingStats {
  verified_theorems: number;
  active_workers: number;
  contributors: number;
  verified_24h: number;
  verified_1h: number;
  last_verified_at: string | null;
  last_verified_domain: string | null;
  by_domain_24h: DomainCount[];
  funnel_24h: FunnelStats;
}

export interface DomainCount {
  domain: string;
  count: number;
}

export interface FunnelStats {
  submitted_24h: number;
  verified_24h: number;
  rejected_24h: number;
  pending_now: number;
}

export interface AuthUser {
  id: string;
  email: string;
  display_name: string | null;
  created_at: string;
  firebase_uid: string;
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

export interface Contributor {
  user_id: string;
  display_name: string | null;
  handle: string;
  worker_count: number;
  theorems_contributed: number;
  active_worker_count: number;
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
  /** Reputation score in [0, 1]. EMA over the worker's lake-promotion
   *  spot-check outcomes. ≥0.9 = trusted; <0.5 = ingest gated; <0.2 +
   *  5 consecutive failures = auto-revoked. Optional because legacy
   *  rows may not have it populated yet. */
  reputation_score?: number;
  spot_check_pass_count?: number;
  spot_check_fail_count?: number;
  auto_revoked_at?: string | null;
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

// --- /api/search ---

export type SearchInputFormat = 'latex' | 'math' | 'sexpr' | 'form';

export interface SearchFilters {
  domain: string | null;
  /** 7-vector dimension (length, mass, time, current, temp, amount, lum). */
  dimension: number[] | null;
  axioms_required: string[];
  max_depth: number | null;
}

export interface SearchRequest {
  input: string;
  input_format: SearchInputFormat;
  filters: SearchFilters;
  limit?: number;
}

export type SearchTier = 'exact' | 'unify' | 'near_miss' | 'empty';

export type SearchMatchKind =
  | { kind: 'exact' }
  | { kind: 'unify'; bindings: Record<string, string> }
  | {
      kind: 'near_miss';
      score: number;
      token_distance: number;
      dim_hamming: number;
      axiom_jaccard: number;
    };

export interface SearchMatchItem {
  id: string;
  canonical_statement: string;
  statement_latex: string | null;
  domain: string;
  dimension: number[] | null;
  depth: number | null;
  axioms_used: string[];
  match: SearchMatchKind;
  lean_url: string;
  proof_url: string;
}

export interface SearchResponse {
  tier: SearchTier;
  matches: SearchMatchItem[];
  took_ms: number;
  parse_error: string | null;
  applied_filters: SearchFilters;
}

// --- /api/me/llm-keys ---

export type LlmProviderName = 'anthropic' | 'openai' | 'ollama';

export interface LlmKeySummary {
  /** Stable provider identifier; one of the three first-class names. */
  provider: string;
  /** Last 4 plaintext chars; never the full key. */
  key_hint: string;
  created_at: string;
  last_used_at: string | null;
}

export interface LlmKeysListResponse {
  keys: LlmKeySummary[];
  /** Provider names the server's `Registry` knows about. */
  known_providers: string[];
}

// --- /api/conjecture ---

export interface BudgetSpec {
  wall_seconds: number;
  max_candidates: number;
}

/**
 * One LLM-proposed seed for a conjecture run. The LLM's contract; not a
 * proof. The GA consumes the chosen suggestion as its starting axiom
 * subset + initial population + mutation priors.
 */
export interface LlmSuggestion {
  axiom_set: string[];
  initial_population: string[];
  mutation_priors: Record<string, number>;
  target_shape: string | null;
  rationale: string;
}

export interface CreateConjectureRequest {
  hunch: string;
  domain_hint?: string | null;
  provider: string;
  model: string;
  budget: BudgetSpec;
}

export interface CreateConjectureResponse {
  job_id: string;
  state: string;
  suggestions: LlmSuggestion[];
}

export type ConjectureState =
  | 'Created'
  | 'LlmComplete'
  | 'QueuedForWorker'
  | 'Running'
  | 'Complete';

export interface ConjectureView {
  id: string;
  state: ConjectureState | string;
  outcome: string | null;
  hunch: string;
  domain_hint: string | null;
  provider: string;
  model: string;
  suggestions: LlmSuggestion[] | null;
  chosen_index: number | null;
  budget: BudgetSpec;
  candidates_attempted: number;
  candidates_verified: number;
  /** Hex-encoded 8-byte theorem IDs. */
  verified_theorem_ids: string[];
  /** Phase E: worker handle while a job is `Running`. */
  claimed_by: string | null;
  last_heartbeat_at: string | null;
  lease_expires_at: string | null;
  created_at: string;
  completed_at: string | null;
}

export interface ConjectureListResponse {
  conjectures: ConjectureView[];
}

export interface StartConjectureRequest {
  chosen_index: number;
  seed_overrides?: unknown;
}

// --- /api/search/concept ---

export interface ConceptHit {
  theorem_id: string;
  canonical_statement: string;
  latex: string | null;
  domain: string;
  /** "Verified" | "Pending" | "Rejected" | "Timeout" — string fallback for forward-compat. */
  status: string;
  depth: number | null;
  /** Combined score in [0, 1]. Higher = better match. */
  score: number;
  /** Which signal flagged it: "embed" | "text" | "both". */
  source: 'embed' | 'text' | 'both';
}

export interface ConceptSearchResponse {
  query: string;
  hits: ConceptHit[];
  took_ms: number;
  embed_available: boolean;
}

export type ConjectureEventKind = 'state_change' | 'progress' | 'candidate_verified' | 'complete';

/** Shape of one event in the SSE stream. */
export interface ConjectureSseEvent {
  id: number;
  kind: ConjectureEventKind | string;
  payload: unknown;
  at: string;
}

// --- Paid Researcher tier (/api/research/jobs) -----------------------------

/** Mirrors `nasrudin_pg::entity::conjecture_jobs::Model`. */
export interface ResearchJob {
  id: string;
  owner_id: string;
  state: string; // queued | claimed | running | proved | budget_exhausted | cancelled
  outcome: string | null;
  hunch: string;
  domain_hint: string | null;
  candidates_attempted: number;
  candidates_verified: number;
  verified_theorem_ids: number[][] | null;
  lake_slot_hours_quota: number;
  lake_slot_hours_consumed: number;
  slice_priority: number;
  tier: string;
  created_at: string;
  completed_at: string | null;
  claimed_by: string | null;
  claimed_at: string | null;
  lease_expires_at: string | null;
  last_heartbeat_at: string | null;
}

export interface CreateResearchJobRequest {
  hunch: string;
  domain_hint?: string | null;
}

export interface CreateResearchJobResponse {
  job_id: string;
  state: string;
}

/**
 * Per-job SSE event shape. Mirrors `physics_api::jobs::JobEvent` —
 * the `kind` discriminator + payload fields land flat in the JSON
 * body (serde tag = "kind", rename_all = "snake_case").
 */
export type ResearchJobEvent =
  | { kind: 'job_state'; state: string }
  | {
      kind: 'progress';
      candidates_attempted: number;
      candidates_verified: number;
      best_fitness: number;
      best_chain_length: number;
      lake_slot_hours_consumed: number;
    }
  | { kind: 'theorem_verified'; theorem_id_hex: string; statement_latex: string }
  | { kind: 'proved'; lean_url: string }
  | { kind: 'budget_exhausted'; best_partial_summary: string; refund_credits: number }
  | { kind: 'cancelled' };
