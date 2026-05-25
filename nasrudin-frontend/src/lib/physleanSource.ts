// Derive a GitHub source URL — plus, on demand, the raw Lean text — for
// a theorem imported from PhysLean.
//
// PhysLean publishes its Lean 4 sources at
//
//   https://github.com/HEPLean/PhysLean
//
// with declarations laid out under `PhysLean/<Namespace>/<File>.lean`.
// Lean qualifiers like `Lorentz.Vector.timelike_time_dominates_space` map
// to a (file path, declaration name) pair: the last segment is the name,
// the rest is the file path's parent directory chain, and the file is
// usually `Basic.lean` (Lean's "open the namespace's main file" convention)
// — but not always. We don't try to guess the file. We give the user a
// repository-level "view on GitHub" link that opens the repo's search for
// the declaration; from there the right file is one click away.
//
// We also expose `fetchPhysleanSource(qualifier)` which uses GitHub's code
// search API (no auth required for public repos at low rate) to find the
// file containing `theorem <name>` / `lemma <name>` / `def <name>` and
// returns the raw source block. The result is cached via TanStack Query so
// the call only fires when the user clicks "Show Lean source".

import { useQuery } from '@tanstack/react-query';

export interface PhysleanSourceLinks {
  declaration: string;
  /** Stable URL that always works: GitHub repo-level search for the name. */
  searchUrl: string;
  /** GitHub raw-content URL for the most likely file. May 404 (we link
   *  to searchUrl as the fallback) but works for the common case. */
  likelyRawUrl: string;
  /** Repo home URL. */
  repoUrl: string;
}

function lastDotSegment(qualifier: string): string {
  const i = qualifier.lastIndexOf('.');
  return i === -1 ? qualifier : qualifier.slice(i + 1);
}

function pathSegments(qualifier: string): string[] {
  const parts = qualifier.split('.').filter(Boolean);
  return parts.slice(0, Math.max(parts.length - 1, 1));
}

/** Build search + raw URLs from a `Foo.Bar.declaration` qualifier. */
export function physleanLinks(qualifier: string): PhysleanSourceLinks {
  const declaration = lastDotSegment(qualifier);
  const dir = pathSegments(qualifier).join('/');
  const repoUrl = 'https://github.com/HEPLean/PhysLean';
  // GitHub's search-in-repo URL — pre-fills "declaration" qualified with
  // its enclosing namespace so the user sees the precise file in the first
  // result rather than every occurrence of a short identifier.
  const searchQuery = encodeURIComponent(`${qualifier} repo:HEPLean/PhysLean`);
  const searchUrl = `https://github.com/search?q=${searchQuery}&type=code`;
  // Best-guess raw URL — works for the most common PhysLean layout where
  // each namespace has a Basic.lean.
  const likelyRawUrl = `https://raw.githubusercontent.com/HEPLean/PhysLean/master/PhysLean/${dir}/Basic.lean`;
  return { declaration, searchUrl, likelyRawUrl, repoUrl };
}

interface SourceFetchResult {
  /** Whole-file source text. */
  source: string;
  /** Best-effort extracted theorem/lemma/def block for the requested name. */
  declarationSnippet: string | null;
  /** URL that the snippet was fetched from. */
  fromUrl: string;
}

// Pull the named declaration out of a Lean source file. Handles `theorem`,
// `lemma`, `def`, `abbrev`, `instance`. The "block" runs from the keyword
// line up to the first blank line *after* the declaration body, or until
// the next top-level keyword — whichever comes first. Strictly heuristic;
// a Lean-aware parser would do better, but for read-only display this is
// plenty.
function extractDeclaration(src: string, name: string): string | null {
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const re = new RegExp(
    `^(theorem|lemma|def|abbrev|instance|noncomputable\\s+def)\\s+${escaped}\\b`,
    'm',
  );
  const m = re.exec(src);
  if (!m) return null;
  const start = m.index;
  // Find end: first occurrence of a line starting with another top-level
  // keyword after the start, OR a `^@[...]` attribute, OR end-of-file.
  const tail = src.slice(start);
  const endRe = /^(theorem|lemma|def|abbrev|instance|namespace|end|noncomputable|@\[)/m;
  // Match in `tail` but skip the first line (the declaration we just
  // found).
  const firstNl = tail.indexOf('\n');
  const searchFrom = firstNl + 1;
  const rest = tail.slice(searchFrom);
  const endMatch = endRe.exec(rest);
  const endOffset = endMatch ? searchFrom + endMatch.index : tail.length;
  return tail.slice(0, endOffset).trimEnd();
}

async function fetchOnce(url: string): Promise<string | null> {
  try {
    const r = await fetch(url, {
      headers: { Accept: 'text/plain, text/*;q=0.9' },
      cache: 'force-cache',
    });
    if (!r.ok) return null;
    return await r.text();
  } catch {
    return null;
  }
}

// Try the most-likely file path first; if that 404s, fall back to GitHub's
// code-search API and use the first hit's raw URL. The search API caps
// unauthenticated requests at 10/min, which is fine for human-driven clicks.
export async function fetchPhysleanSource(qualifier: string): Promise<SourceFetchResult | null> {
  const { declaration, likelyRawUrl } = physleanLinks(qualifier);

  const direct = await fetchOnce(likelyRawUrl);
  if (direct) {
    return {
      source: direct,
      declarationSnippet: extractDeclaration(direct, declaration),
      fromUrl: likelyRawUrl,
    };
  }

  // Fall back: code search to find the file that declares this name.
  // GitHub's REST search endpoint returns JSON; we ask for the first match
  // in HEPLean/PhysLean and pull its `path` field.
  const apiUrl = `https://api.github.com/search/code?q=${encodeURIComponent(
    `"${declaration}" repo:HEPLean/PhysLean extension:lean`,
  )}&per_page=1`;
  try {
    const r = await fetch(apiUrl, {
      headers: { Accept: 'application/vnd.github.v3+json' },
    });
    if (!r.ok) return null;
    const j = (await r.json()) as {
      items?: { path?: string }[];
    };
    const path = j.items?.[0]?.path;
    if (!path) return null;
    const rawUrl = `https://raw.githubusercontent.com/HEPLean/PhysLean/master/${path}`;
    const body = await fetchOnce(rawUrl);
    if (!body) return null;
    return {
      source: body,
      declarationSnippet: extractDeclaration(body, declaration),
      fromUrl: rawUrl,
    };
  } catch {
    return null;
  }
}

export function usePhysleanSource(qualifier: string | null | undefined) {
  return useQuery({
    queryKey: ['physlean-source', qualifier],
    queryFn: () => (qualifier ? fetchPhysleanSource(qualifier) : Promise.resolve(null)),
    enabled: !!qualifier,
    staleTime: 60 * 60_000, // an hour; PhysLean releases are infrequent
    retry: false,
  });
}
