import { useMutation, useQuery, useQueryClient } from '@tanstack/react-query';
import { apiFetch, isApiError } from './api';
import type {
  ApiKeySummary,
  AuthUser,
  ConceptSearchResponse,
  ConjectureListResponse,
  ConjectureView,
  CreateConjectureRequest,
  CreateConjectureResponse,
  CreateResearchJobRequest,
  CreateResearchJobResponse,
  DbStats,
  LlmKeysListResponse,
  MeProfile,
  MeStats,
  NewApiKey,
  ResearchJob,
  SavedSearch,
  SearchRequest,
  SearchResponse,
  StartConjectureRequest,
  Theorem,
  TheoremListResponse,
  UserProfileFields,
  Worker,
} from './types';

// --- auth ---

export const meQueryKey = ['me'] as const;

export function useMe() {
  return useQuery<AuthUser | null>({
    queryKey: meQueryKey,
    queryFn: async () => {
      try {
        return await apiFetch<AuthUser>('/api/auth/me');
      } catch (e) {
        if (isApiError(e) && e.status === 401) return null;
        throw e;
      }
    },
    staleTime: 60_000,
  });
}

export function useLogin() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (creds: { email: string; password: string }) =>
      apiFetch<AuthUser>('/api/auth/login', { method: 'POST', body: JSON.stringify(creds) }),
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

export function useRegister() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (input: { email: string; password: string; display_name?: string }) =>
      apiFetch<AuthUser>('/api/auth/register', { method: 'POST', body: JSON.stringify(input) }),
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

export function useLogout() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: () => apiFetch<{ logged_out: true }>('/api/auth/logout', { method: 'POST' }),
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

// --- theorems ---

export function useRecentTheorems(limit = 20) {
  return useQuery({
    queryKey: ['theorems', 'recent', limit],
    queryFn: () => apiFetch<TheoremListResponse>(`/api/theorems/recent?limit=${limit}`),
  });
}

export function useTheorem(id: string) {
  return useQuery({
    queryKey: ['theorem', id],
    queryFn: () => apiFetch<Theorem>(`/api/theorems/${id}`),
    enabled: !!id,
  });
}

export function useDomains() {
  return useQuery({
    queryKey: ['domains'],
    queryFn: () => apiFetch<Record<string, number>>('/api/domains'),
  });
}

// --- api keys ---

export function useApiKeys() {
  return useQuery({
    queryKey: ['api-keys'],
    queryFn: () => apiFetch<{ keys: ApiKeySummary[] }>('/api/api-keys'),
  });
}

export function useCreateApiKey() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: { name: string; kind?: 'live' | 'worker'; expires_in_days?: number }) =>
      apiFetch<NewApiKey>('/api/api-keys', { method: 'POST', body: JSON.stringify(body) }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['api-keys'] }),
  });
}

export function useRevokeApiKey() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (id: string) =>
      apiFetch<{ revoked: true }>(`/api/api-keys/${id}`, { method: 'DELETE' }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['api-keys'] }),
  });
}

// --- saved searches ---

export function useSavedSearches() {
  return useQuery({
    queryKey: ['saved-searches'],
    queryFn: () => apiFetch<{ saved_searches: SavedSearch[] }>('/api/saved-searches'),
  });
}

// --- library: saved theorems + folders ---

export interface LibraryFolder {
  id: string;
  user_id: string;
  name: string;
  color: string | null;
  created_at: string;
  updated_at: string;
}

export interface SavedTheoremRow {
  theorem: Theorem;
  saved_at: string;
  folder_id: string | null;
  note: string | null;
  label: string | null;
}

export interface LibraryListResponse {
  saved: SavedTheoremRow[];
  count: number;
  limit: number;
  plan_tier: string;
}

export interface LibraryFoldersResponse {
  folders: LibraryFolder[];
}

export const libraryQueryKey = (folderId?: string) =>
  folderId ? (['library', 'theorems', folderId] as const) : (['library', 'theorems'] as const);

export function useLibraryTheorems(folderId?: string) {
  const qs = folderId ? `?folder_id=${encodeURIComponent(folderId)}` : '';
  return useQuery({
    queryKey: libraryQueryKey(folderId),
    queryFn: () => apiFetch<LibraryListResponse>(`/api/me/library/theorems${qs}`),
  });
}

export function useLibraryFolders() {
  return useQuery({
    queryKey: ['library', 'folders'],
    queryFn: () => apiFetch<LibraryFoldersResponse>('/api/me/library/folders'),
  });
}

export interface LibraryFullError {
  error: 'library_full';
  limit: number;
  saved: number;
  plan_tier: string;
  upgrade_to: string;
}

export function useSaveTheorem() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: {
      theorem_id: string;
      folder_id?: string | null;
      note?: string | null;
      label?: string | null;
    }) =>
      apiFetch<{ saved: true; saved_count?: number; limit?: number; already_saved?: boolean }>(
        '/api/me/library/theorems',
        { method: 'POST', body: JSON.stringify(body) },
      ),
    onSuccess: () => {
      qc.invalidateQueries({ queryKey: ['library'] });
    },
  });
}

export function useUnsaveTheorem() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (theoremIdHex: string) =>
      apiFetch<{ deleted: true }>(`/api/me/library/theorems/${theoremIdHex}`, { method: 'DELETE' }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['library'] }),
  });
}

export function usePatchSavedTheorem() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: ({
      theoremIdHex,
      patch,
    }: {
      theoremIdHex: string;
      patch: {
        folder_id?: string | null;
        note?: string | null;
        label?: string | null;
      };
    }) =>
      apiFetch(`/api/me/library/theorems/${theoremIdHex}`, {
        method: 'PATCH',
        body: JSON.stringify(patch),
      }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['library'] }),
  });
}

export function useCreateFolder() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: { name: string; color?: string | null }) =>
      apiFetch<LibraryFolder>('/api/me/library/folders', {
        method: 'POST',
        body: JSON.stringify(body),
      }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['library'] }),
  });
}

export function useDeleteFolder() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (id: string) =>
      apiFetch<{ deleted: true }>(`/api/me/library/folders/${id}`, { method: 'DELETE' }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['library'] }),
  });
}

export function usePatchFolder() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: ({
      id,
      patch,
    }: {
      id: string;
      patch: { name?: string; color?: string | null };
    }) =>
      apiFetch<LibraryFolder>(`/api/me/library/folders/${id}`, {
        method: 'PATCH',
        body: JSON.stringify(patch),
      }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['library'] }),
  });
}

// --- workers ---

export function useWorkers() {
  return useQuery({
    queryKey: ['workers'],
    queryFn: () => apiFetch<Worker[]>('/api/workers'),
    refetchInterval: 30_000,
  });
}

// --- stats ---

export function useStats() {
  return useQuery({
    queryKey: ['stats'],
    queryFn: () => apiFetch<DbStats>('/api/stats'),
    refetchInterval: 60_000,
  });
}

// --- me/stats ---

export function useMeStats() {
  return useQuery({
    queryKey: ['me', 'stats'],
    queryFn: () => apiFetch<MeStats>('/api/me/stats'),
  });
}

// --- profile editing ---

export const meProfileQueryKey = ['me', 'profile'] as const;

export function useMeProfile() {
  return useQuery({
    queryKey: meProfileQueryKey,
    queryFn: () => apiFetch<MeProfile>('/api/me/profile'),
  });
}

export function useUpdateMeProfile() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: { display_name?: string | null; profile?: UserProfileFields }) =>
      apiFetch<MeProfile>('/api/me/profile', {
        method: 'PATCH',
        body: JSON.stringify(body),
      }),
    onSuccess: () => {
      qc.invalidateQueries({ queryKey: meProfileQueryKey });
      qc.invalidateQueries({ queryKey: meQueryKey });
    },
  });
}

// --- workers I own (joined via api_keys.kind = 'worker', user_id = me) ---

export function useMyWorkers() {
  return useQuery({
    queryKey: ['me', 'workers'],
    queryFn: () => apiFetch<{ workers: Worker[] }>('/api/me/workers'),
    refetchInterval: 30_000,
  });
}

// --- /api/search ---

/**
 * Conjecture-to-proof search. POST request with the parsed input + filters;
 * server runs three tiers (AC-exact → unification → near-miss ranking) and
 * returns whichever has hits, plus the parse error if any. Modeled as a
 * mutation rather than a query because the body is large/structured and we
 * want explicit submit semantics rather than auto-refetch.
 */
export function useSearch() {
  return useMutation({
    mutationFn: (req: SearchRequest) =>
      apiFetch<SearchResponse>('/api/search', {
        method: 'POST',
        body: JSON.stringify(req),
      }),
  });
}

// --- /api/me/llm-keys ---

export const llmKeysQueryKey = ['llm-keys'] as const;

export function useLlmKeys() {
  return useQuery<LlmKeysListResponse>({
    queryKey: llmKeysQueryKey,
    queryFn: () => apiFetch<LlmKeysListResponse>('/api/me/llm-keys'),
  });
}

export function useSetLlmKey() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: { provider: string; key: string }) =>
      apiFetch<{ provider: string; key_hint: string }>('/api/me/llm-keys', {
        method: 'POST',
        body: JSON.stringify(body),
      }),
    onSuccess: () => qc.invalidateQueries({ queryKey: llmKeysQueryKey }),
  });
}

export function useRevokeLlmKey() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async (provider: string) => {
      try {
        await apiFetch<unknown>(`/api/me/llm-keys/${provider}`, { method: 'DELETE' });
      } catch (e) {
        if (isApiError(e) && e.status === 404) return; // already gone
        throw e;
      }
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: llmKeysQueryKey }),
  });
}

// --- /api/search/concept ---

export function useConceptSearch(
  query: string,
  opts: { includePending?: boolean; limit?: number; enabled?: boolean } = {},
) {
  const includePending = opts.includePending ?? true;
  const limit = opts.limit ?? 30;
  const enabled = opts.enabled ?? query.trim().length > 0;
  const params = new URLSearchParams({
    q: query,
    include_pending: String(includePending),
    limit: String(limit),
  });
  return useQuery<ConceptSearchResponse>({
    queryKey: ['concept-search', query, includePending, limit],
    queryFn: () => apiFetch<ConceptSearchResponse>(`/api/search/concept?${params}`),
    enabled,
    staleTime: 30_000,
  });
}

// --- /api/conjecture ---

export const conjecturesQueryKey = ['conjectures'] as const;

export function useMyConjectures() {
  return useQuery<ConjectureListResponse>({
    queryKey: conjecturesQueryKey,
    queryFn: () => apiFetch<ConjectureListResponse>('/api/me/conjectures'),
    refetchInterval: 30_000,
  });
}

export function useConjecture(id: string) {
  return useQuery<ConjectureView>({
    queryKey: ['conjecture', id],
    queryFn: () => apiFetch<ConjectureView>(`/api/conjecture/${id}`),
    enabled: !!id,
  });
}

export function useCreateConjecture() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: CreateConjectureRequest) =>
      apiFetch<CreateConjectureResponse>('/api/conjecture', {
        method: 'POST',
        body: JSON.stringify(body),
      }),
    onSuccess: () => qc.invalidateQueries({ queryKey: conjecturesQueryKey }),
  });
}

/** Phase F: trigger paper-draft generation. Returns 202; the actual
 *  draft streams via the /sse channel as `paper_chunk` events.
 */
export function useStartPaperDraft(id: string) {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: () =>
      apiFetch<{ job_id: string; state: string }>(`/api/conjecture/${id}/paper`, {
        method: 'POST',
      }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['conjecture', id] }),
  });
}

export function useStartConjecture(id: string) {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: StartConjectureRequest) =>
      apiFetch<{ id: string; state: string }>(`/api/conjecture/${id}/start`, {
        method: 'POST',
        body: JSON.stringify(body),
      }),
    onSuccess: () => {
      qc.invalidateQueries({ queryKey: ['conjecture', id] });
      qc.invalidateQueries({ queryKey: conjecturesQueryKey });
    },
  });
}

// --- Paid Researcher tier (/api/research/jobs) ---

export const researchJobsQueryKey = ['research-jobs'] as const;

export function useResearchJobs() {
  return useQuery<{ jobs: ResearchJob[] }>({
    queryKey: researchJobsQueryKey,
    queryFn: () => apiFetch<{ jobs: ResearchJob[] }>('/api/research/jobs'),
    refetchInterval: 30_000,
  });
}

export function useResearchJob(id: string | null) {
  return useQuery<ResearchJob>({
    queryKey: ['research-job', id],
    queryFn: () => apiFetch<ResearchJob>(`/api/research/jobs/${id}`),
    enabled: !!id,
    refetchInterval: (q) => {
      // Stop polling once the job hits a terminal state — SSE feeds
      // live updates anyway.
      const data = q.state.data as ResearchJob | undefined;
      if (!data) return 5_000;
      const terminal = ['proved', 'budget_exhausted', 'cancelled', 'Complete'];
      return terminal.includes(data.state) ? false : 10_000;
    },
  });
}

export function useCreateResearchJob() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (body: CreateResearchJobRequest) =>
      apiFetch<CreateResearchJobResponse>('/api/research/jobs', {
        method: 'POST',
        body: JSON.stringify(body),
      }),
    onSuccess: () => {
      qc.invalidateQueries({ queryKey: researchJobsQueryKey });
      qc.invalidateQueries({ queryKey: meProfileQueryKey });
    },
  });
}

export function useCancelResearchJob() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: (id: string) =>
      apiFetch<{ cancelled: true; refunded: boolean }>(`/api/research/jobs/${id}/cancel`, {
        method: 'POST',
      }),
    onSuccess: (_data, id) => {
      qc.invalidateQueries({ queryKey: researchJobsQueryKey });
      qc.invalidateQueries({ queryKey: ['research-job', id] });
      qc.invalidateQueries({ queryKey: meProfileQueryKey });
    },
  });
}

// --- /api/featured ---

export function useFeaturedDiscoveries() {
  return useQuery({
    queryKey: ['featured'],
    queryFn: () => apiFetch<Array<{
      formula: string;
      name: string;
      domain: string;
      found: boolean;
      cycle: string;
      elapsed: string;
      proof_lines?: number;
      note: string;
    }>>('/api/featured'),
    staleTime: 300_000, // 5 minutes
  });
}

// --- live event streams (SSE) ---

export {
  useConjectureStream,
  useDiscoveryFeed,
  useResearchJobStream,
  useStatsStream,
} from './sse';
