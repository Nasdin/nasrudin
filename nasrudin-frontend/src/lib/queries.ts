import {
  queryOptions,
  useInfiniteQuery,
  useMutation,
  useQuery,
  useQueryClient,
} from '@tanstack/react-query';
import { apiFetch, isApiError } from './api';
import {
  firebaseSignOut,
  getCurrentIdToken,
  sendPasswordReset,
  sendVerificationEmail,
  signInWithEmail,
  signInWithGoogle,
  signUpWithEmail,
} from './firebase';
import type {
  ApiKeySummary,
  AuthUser,
  ConceptSearchResponse,
  ConjectureListResponse,
  ConjectureView,
  Contributor,
  CreateConjectureRequest,
  CreateConjectureResponse,
  CreateResearchJobRequest,
  CreateResearchJobResponse,
  DbStats,
  LandingStats,
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
    // Auth identity rarely flips inside a session; mutations
    // (login/logout/profile-update) explicitly invalidate this key.
    staleTime: 3 * 60_000,
  });
}

/**
 * Sign in with email + password. Calls Firebase, then exchanges the ID
 * token for a session cookie via POST /api/auth/firebase-session. The
 * `useMe` query is invalidated so the new identity propagates.
 */
export function useLogin() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async (creds: { email: string; password: string }) => {
      await signInWithEmail(creds.email, creds.password);
      const idToken = await getCurrentIdToken();
      return apiFetch<AuthUser>('/api/auth/firebase-session', {
        method: 'POST',
        body: JSON.stringify({ id_token: idToken }),
      });
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

/**
 * Create a new account with email + password. Sends the verification
 * email automatically. The session-exchange call returns 403
 * `email_not_verified` until the user clicks the link; the form catches
 * that and shows the verify-your-email alert.
 */
export function useRegister() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async (input: { email: string; password: string }) => {
      await signUpWithEmail(input.email, input.password);
      await sendVerificationEmail();
      const idToken = await getCurrentIdToken();
      try {
        return await apiFetch<AuthUser>('/api/auth/firebase-session', {
          method: 'POST',
          body: JSON.stringify({ id_token: idToken }),
        });
      } catch (e) {
        if (
          isApiError(e) &&
          e.status === 403 &&
          (e.body as { error?: string } | null)?.error === 'email_not_verified'
        ) {
          // Expected — frontend renders the verification alert.
          return null;
        }
        throw e;
      }
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

/** Sign in with Google (popup). Same exchange pattern as useLogin. */
export function useGoogleLogin() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async () => {
      await signInWithGoogle();
      const idToken = await getCurrentIdToken();
      return apiFetch<AuthUser>('/api/auth/firebase-session', {
        method: 'POST',
        body: JSON.stringify({ id_token: idToken }),
      });
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

/** Sign out from both Firebase and the backend session. */
export function useLogout() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: async () => {
      await firebaseSignOut();
      try {
        await apiFetch<{ logged_out: true }>('/api/auth/logout', { method: 'POST' });
      } catch (e) {
        // 401 is expected if the session was already cleared.
        if (!isApiError(e) || e.status !== 401) throw e;
      }
    },
    onSuccess: () => qc.invalidateQueries({ queryKey: meQueryKey }),
  });
}

/** Trigger Firebase to send a password-reset email. Server is not involved. */
export function useResetPassword() {
  return useMutation({
    mutationFn: (email: string) => sendPasswordReset(email),
  });
}

/** Re-send the verification email to the currently signed-in Firebase user. */
export function useResendVerification() {
  return useMutation({
    mutationFn: () => sendVerificationEmail(),
  });
}

// --- public landing stats ---

export function useLandingStats() {
  return useQuery<LandingStats>({
    queryKey: ['stats', 'landing'],
    queryFn: () => apiFetch<LandingStats>('/api/stats/landing'),
    staleTime: 60_000,
    refetchOnWindowFocus: false,
  });
}

// --- theorems ---

/// Factory + hook pair for the recent-theorems list. The factory shape
/// lets TanStack Router route loaders call
/// `queryClient.ensureQueryData(recentTheoremsOptions(limit))` so the
/// `/browse` route prefetches on hover (the router's
/// `defaultPreload: 'intent'` handles the hover trigger), then the
/// component renders from cache instantly on click.
export const recentTheoremsOptions = (limit = 20) =>
  queryOptions({
    queryKey: ['theorems', 'recent', limit] as const,
    queryFn: () => apiFetch<TheoremListResponse>(`/api/theorems/recent?limit=${limit}`),
    // SSE invalidates this key on every theorem_verified event, so the
    // cache stays fresh through ticks; the pull is just for first-paint
    // and reconnect recovery. 5 min is plenty.
    staleTime: 5 * 60_000,
  });

export function useRecentTheorems(limit = 20) {
  return useQuery(recentTheoremsOptions(limit));
}

/// Manual "Verify with Lake" trigger (P-Task 4 endpoint). Enqueues the
/// theorem at priority 0 and waits up to `wait_seconds` synchronously
/// for the kernel verdict. Server returns:
///   - 200 + `{status:"lake_verified", ...}` on success,
///   - 410 + `{status:"rejected", reason}` on kernel reject (cascade
///     ran for the descendants),
///   - 202 on sync-wait timeout (promotion still in flight).
export interface VerifyResponse {
  status?: string;
  reason?: string;
  [key: string]: unknown;
}
export function useVerifyWithLake() {
  const qc = useQueryClient();
  return useMutation({
    mutationFn: ({ idHex, waitSeconds }: { idHex: string; waitSeconds?: number }) =>
      apiFetch<VerifyResponse>(`/api/theorems/${idHex}/verify`, {
        method: 'POST',
        body: JSON.stringify({ wait_seconds: waitSeconds ?? 30 }),
      }),
    onSuccess: (_data, vars) => {
      // Refetch the affected theorem detail + the recent list so
      // VerificationBadge re-renders.
      qc.invalidateQueries({ queryKey: ['theorem', vars.idHex] });
      qc.invalidateQueries({ queryKey: ['theorems', 'recent'] });
    },
  });
}

export function useTheorem(id: string) {
  return useQuery({
    queryKey: ['theorem', id],
    queryFn: () => apiFetch<Theorem>(`/api/theorems/${id}`),
    enabled: !!id,
    staleTime: 10 * 60_000, // 10 minutes - theorems don't change often
  });
}

export function useDomains() {
  return useQuery({
    queryKey: ['domains'],
    queryFn: () => apiFetch<Record<string, number>>('/api/domains'),
    staleTime: 5 * 60_000, // 5 minutes - domains rarely change
  });
}

// --- api keys ---

export function useApiKeys() {
  return useQuery({
    queryKey: ['api-keys'],
    queryFn: () => apiFetch<{ keys: ApiKeySummary[] }>('/api/api-keys'),
    // Keys only change on explicit create/revoke (which invalidate);
    // session views are otherwise read-only.
    staleTime: 3 * 60_000,
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
    // User-owned, mutation-invalidated.
    staleTime: 3 * 60_000,
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

export const libraryTheoremsOptions = (folderId?: string) => {
  const qs = folderId ? `?folder_id=${encodeURIComponent(folderId)}` : '';
  return queryOptions({
    queryKey: libraryQueryKey(folderId),
    queryFn: () => apiFetch<LibraryListResponse>(`/api/me/library/theorems${qs}`),
    // Library is mutation-driven; save/unsave invalidates this key.
    staleTime: 5 * 60_000,
  });
};

export function useLibraryTheorems(folderId?: string) {
  return useQuery(libraryTheoremsOptions(folderId));
}

export const libraryFoldersOptions = () =>
  queryOptions({
    queryKey: ['library', 'folders'] as const,
    queryFn: () => apiFetch<LibraryFoldersResponse>('/api/me/library/folders'),
    // Folders rarely change; create/rename/delete mutations invalidate.
    staleTime: 5 * 60_000,
  });

export function useLibraryFolders() {
  return useQuery(libraryFoldersOptions());
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
    mutationFn: ({ id, patch }: { id: string; patch: { name?: string; color?: string | null } }) =>
      apiFetch<LibraryFolder>(`/api/me/library/folders/${id}`, {
        method: 'PATCH',
        body: JSON.stringify(patch),
      }),
    onSuccess: () => qc.invalidateQueries({ queryKey: ['library'] }),
  });
}

// --- workers ---

export const workersOptions = () =>
  queryOptions({
    queryKey: ['workers'] as const,
    queryFn: () => apiFetch<Worker[]>('/api/workers'),
    // Cache hits between 30 s polls = instant render on tab-switch.
    staleTime: 10_000,
    refetchInterval: 30_000,
  });

export function useWorkers() {
  return useQuery(workersOptions());
}

// --- workers (paginated infinite scroll) ---

interface WorkersPageResponse {
  workers: Worker[];
  next_cursor: string | null;
}

export function useInfiniteWorkers() {
  return useInfiniteQuery({
    queryKey: ['workers', 'infinite'] as const,
    queryFn: async ({ pageParam }) => {
      const params = new URLSearchParams();
      params.set('limit', '50');
      if (pageParam) {
        params.set('cursor', pageParam as string);
      }
      return apiFetch<WorkersPageResponse>(`/api/workers?${params.toString()}`);
    },
    initialPageParam: undefined as string | undefined,
    getNextPageParam: (lastPage) => lastPage.next_cursor ?? undefined,
    staleTime: 10_000,
  });
}

// --- contributors (user leaderboard) ---

export const contributorsOptions = () =>
  queryOptions({
    queryKey: ['contributors'] as const,
    queryFn: () => apiFetch<Contributor[]>('/api/contributors'),
    staleTime: 30_000,
    refetchInterval: 60_000,
  });

export function useContributors() {
  return useQuery(contributorsOptions());
}

export function useContributorWorkers(userId: string) {
  return useQuery<Worker[]>({
    queryKey: ['contributors', userId, 'workers'],
    queryFn: () => apiFetch<Worker[]>(`/api/contributors/${userId}`),
    enabled: !!userId,
    staleTime: 10_000,
    refetchInterval: 30_000,
  });
}

// --- stats ---

export function useStats() {
  return useQuery({
    queryKey: ['stats'],
    queryFn: () => apiFetch<DbStats>('/api/stats'),
    staleTime: 20_000,
    refetchInterval: 60_000,
  });
}

// --- me/stats ---

export function useMeStats() {
  return useQuery({
    queryKey: ['me', 'stats'],
    queryFn: () => apiFetch<MeStats>('/api/me/stats'),
    // User-owned aggregate; mutations invalidate.
    staleTime: 2 * 60_000,
  });
}

// --- profile editing ---

export const meProfileQueryKey = ['me', 'profile'] as const;

export function useMeProfile() {
  return useQuery({
    queryKey: meProfileQueryKey,
    queryFn: () => apiFetch<MeProfile>('/api/me/profile'),
    // Profile mutations invalidate; otherwise read-only across a session.
    staleTime: 5 * 60_000,
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
    staleTime: 10_000,
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
    // User-owned credentials; set/revoke mutations invalidate.
    staleTime: 5 * 60_000,
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
    // Search-result keys are query-specific; debouncer already
    // throttles network. 90 s avoids re-fetch when the user retypes
    // the same query after a brief detour.
    staleTime: 90_000,
    // While the user types and the debouncer fires, show the previous
    // results instead of a loading flicker until the new ones arrive.
    placeholderData: (prev) => prev,
  });
}

// --- /api/conjecture ---

export const conjecturesQueryKey = ['conjectures'] as const;

export function useMyConjectures() {
  return useQuery<ConjectureListResponse>({
    queryKey: conjecturesQueryKey,
    queryFn: () => apiFetch<ConjectureListResponse>('/api/me/conjectures'),
    staleTime: 10_000,
    refetchInterval: 30_000,
  });
}

export function useConjecture(id: string) {
  return useQuery<ConjectureView>({
    queryKey: ['conjecture', id],
    queryFn: () => apiFetch<ConjectureView>(`/api/conjecture/${id}`),
    enabled: !!id,
    staleTime: 30_000,
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
    staleTime: 10_000,
    refetchInterval: 30_000,
  });
}

export function useResearchJob(id: string | null) {
  return useQuery<ResearchJob>({
    queryKey: ['research-job', id],
    queryFn: () => apiFetch<ResearchJob>(`/api/research/jobs/${id}`),
    enabled: !!id,
    staleTime: 5_000,
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
    queryFn: () =>
      apiFetch<
        Array<{
          formula: string;
          name: string;
          domain: string;
          found: boolean;
          cycle: string;
          elapsed: string;
          proof_lines?: number;
          note: string;
        }>
      >('/api/featured'),
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

// --- billing ---

export interface BillingMe {
  plan_tier: 'free' | 'researcher' | 'institution' | 'enterprise';
  current_period_end: string | null;
  targeted_searches_used: number;
  targeted_searches_limit: number;
  api_used_today: number;
  api_limit_per_day: number;
}

export function useBillingMe() {
  return useQuery<BillingMe>({
    queryKey: ['billing', 'me'],
    queryFn: () => apiFetch<BillingMe>('/api/billing/me'),
    // Stripe webhooks invalidate this; sub state otherwise stable
    // across a session.
    staleTime: 3 * 60_000,
  });
}

// --- public sponsorship ---

/**
 * Public-profile sponsorship summary. Active subscription tier is
 * the latest `kind='subscription' AND status='active'` row;
 * lifetime totals roll up every donation + (current OR ended)
 * subscription's per-interval price. Stripe-side ids are NOT
 * exposed here — only the aggregate badge fields.
 */
export type SponsorTier =
  | 'sponsor_5'
  | 'sponsor_25'
  | 'sponsor_100'
  | 'sponsor_open'
  | 'researcher_monthly'
  | 'researcher_annual';

export interface PublicSponsorshipSummary {
  active_tier: SponsorTier | string | null;
  active_amount_cents: number | null;
  lifetime_total_cents: number;
  donation_count: number;
  first_supported_at: string | null;
  latest_supported_at: string | null;
}

export function useUserSponsorship(userId: string | null | undefined) {
  return useQuery<PublicSponsorshipSummary>({
    queryKey: ['users', userId, 'sponsorship'],
    queryFn: () =>
      apiFetch<PublicSponsorshipSummary>(`/api/users/${userId}/sponsorship`),
    enabled: !!userId,
    // Public profile data — Stripe webhook updates land within a few
    // minutes, but for badge rendering 5 min staleness is fine.
    staleTime: 5 * 60_000,
  });
}
