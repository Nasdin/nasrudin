import { useMutation, useQuery, useQueryClient } from '@tanstack/react-query';
import { apiFetch, isApiError } from './api';
import type {
  ApiKeySummary,
  AuthUser,
  ConjectureListResponse,
  ConjectureView,
  CreateConjectureRequest,
  CreateConjectureResponse,
  LlmKeysListResponse,
  MeProfile,
  MeStats,
  NewApiKey,
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

// --- workers ---

export function useWorkers() {
  return useQuery({
    queryKey: ['workers'],
    queryFn: () => apiFetch<Worker[]>('/api/workers'),
    refetchInterval: 30_000,
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

// --- live event streams (SSE) ---

export { useConjectureStream, useDiscoveryFeed, useStatsStream } from './sse';
