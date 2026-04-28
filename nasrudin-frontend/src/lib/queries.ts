import { useMutation, useQuery, useQueryClient } from '@tanstack/react-query';
import { apiFetch, isApiError } from './api';
import type {
  ApiKeySummary,
  AuthUser,
  MeStats,
  NewApiKey,
  SavedSearch,
  Theorem,
  TheoremListResponse,
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

// --- live event streams (SSE) ---

export { useDiscoveryFeed, useStatsStream } from './sse';
