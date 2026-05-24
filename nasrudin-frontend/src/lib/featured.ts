export interface Rediscovery {
  formula: string;
  name: string;
  domain: string;
  found: boolean;
  cycle: string;
  elapsed: string;
  proofLines?: number;
  /** Hex theorem id when `found = true`. Drives the landing-page
   *  card link to `/theorem/$id`. Undefined when still searching. */
  theoremId?: string;
  /** Count of axioms the matched GA chain composed. Undefined when
   *  still searching. */
  axiomsUsed?: number;
  note: string;
}

// This is now fetched from /api/featured instead of being hardcoded
// Keeping the interface for type safety
export const FEATURED_REDISCOVERIES: Rediscovery[] = [];
