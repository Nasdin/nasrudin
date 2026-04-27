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

export interface Theorem {
  id: string;
  domain: Domain;
  statement: { Lean: string } | { Latex: string } | { Plain: string };
  proof?: ProofTree;
  verified: VerificationStatus;
  generation: number;
  depth: number;
  parents: string[];
  created_at: string;
}

export type ProofTree = unknown;

export type VerificationStatus =
  | { Verified: { proof_term: string; tactic_used: string } }
  | { Rejected: { reason: string } }
  | 'Pending';

export interface AuthUser {
  id: string;
  email: string;
  display_name: string | null;
  created_at: string;
}

export interface ApiKeySummary {
  id: string;
  name: string;
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

export interface Worker {
  id: string;
  name: string | null;
  host: string | null;
  last_seen: string;
  theorems_contributed: number;
  status: 'Active' | 'Inactive' | 'Disconnected' | 'active' | 'inactive' | 'disconnected';
}

export interface MeStats {
  saved_searches: number;
  api_keys: number;
}
