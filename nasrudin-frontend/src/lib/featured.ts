export interface Rediscovery {
  formula: string;
  name: string;
  domain: string;
  found: boolean;
  cycle: string;
  elapsed: string;
  proofLines?: number;
  note: string;
}

// This is now fetched from /api/featured instead of being hardcoded
// Keeping the interface for type safety
export const FEATURED_REDISCOVERIES: Rediscovery[] = [];
