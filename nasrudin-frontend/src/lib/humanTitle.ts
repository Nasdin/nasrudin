// Convert a Lean qualifier into a humanised page title.
//
// A theorem like `Lorentz.Vector.timelike_time_dominates_space` ships from
// PhysLean as an identifier that only a Lean engineer can parse. For a
// visiting professor we want to surface "Timelike vectors dominate space"
// (or close). Same for `mem_iff_mem_toMultiset` →
// "Member iff member of toMultiset".
//
// The algorithm is deliberately conservative — we don't try to be a
// natural-language generator. We just:
//   1. Take the meaningful trailing segments of the dotted qualifier,
//      dropping the namespace prefix (e.g. drop `Lorentz.Vector.`).
//   2. Strip boilerplate suffixes Lean autogenerates (`.eq_1`, `.def_2`,
//      `.proof_3`).
//   3. Split snake_case into words.
//   4. Expand a small lookup of physics shorthands (`em` → "electro-
//      magnetic", `sr` → "special relativity") so the prose reads.
//   5. Sentence-case the result.
//
// Falls back to the last segment unchanged if it can't make anything
// human out of the input.

const GENERIC_SUFFIX =
  /^(eq|def|lemma|theorem|prop|propositional|cor|axiom|inst|inst_\d+|congr|spec|aux|sigma|proof)_(\d+|\w+)$/i;

const SHORTHAND: Record<string, string> = {
  em: 'electromagnetic',
  sr: 'special relativistic',
  gr: 'general relativistic',
  qm: 'quantum-mechanical',
  qft: 'quantum-field-theoretic',
  thm: 'theorem',
  prop: 'proposition',
  iff: 'iff',
  eq: 'equation',
  func: 'function',
  fn: 'function',
  hom: 'homomorphism',
  iso: 'isomorphism',
  isom: 'isomorphism',
  inj: 'injective',
  surj: 'surjective',
  bij: 'bijective',
  bilin: 'bilinear',
  comm: 'commutative',
  assoc: 'associative',
  diff: 'differentiable',
  cont: 'continuous',
  meas: 'measurable',
  inv: 'inverse',
  abs: 'absolute',
  norm: 'norm',
  sup: 'supremum',
  inf: 'infimum',
  exp: 'exponential',
  log: 'logarithm',
  poly: 'polynomial',
  // Common Lean math vocab kept short:
  finset: 'finset',
  multiset: 'multiset',
};

// Curated overrides: high-signal statement names where the templated
// breakdown reads weirdly. Add sparingly — only when the template fails.
const OVERRIDE: Record<string, string> = {
  'Lorentz.Vector.timelike_time_dominates_space': 'Timelike vectors have a dominant time component',
  'PhysLean.FourTree.mem_iff_mem_toMultiset': 'A FourTree contains x iff its multiset does',
  'Electromagnetism.ElectromagneticPotential.vectorPotential_differentiable_time':
    'The vector potential is differentiable in time',
  'Lorentz.ContrMod.toFin1dℝ.eq_1':
    'The 1-dim ContrMod equivalence collapses to its underlying map',
  'CliffordAlgebra.range_lift': 'The Clifford algebra’s `range` is the image of `lift`',
  'StandardModel.repU1_fundamentalSU2_commute':
    'U(1) and fundamental SU(2) representations commute on Φ',
  'PhysLean.physHermite_norm_cons': 'Physicist-Hermite polynomials carry the standard L² norm',
};

function splitSnake(word: string): string[] {
  return word.split(/[_-]+/).filter(Boolean);
}

function expandWord(w: string): string {
  const lower = w.toLowerCase();
  const long = SHORTHAND[lower];
  if (long) return long;
  return w;
}

// Sentence-case the assembled phrase (capitalise the first character,
// lowercase the rest unless it's already mixed-case identifier like
// "ContrMod" — preserve those).
function sentenceCase(s: string): string {
  if (!s) return s;
  const first = s.charAt(0).toUpperCase();
  const rest = s.slice(1);
  return first + rest;
}

/**
 * Humanise a Lean qualifier. Empty input → empty output. Curated overrides
 * are returned verbatim when present.
 */
export function leanToHumanTitle(qualified: string | null | undefined): string {
  if (!qualified) return '';
  const override = OVERRIDE[qualified];
  if (override) return override;

  const parts = qualified.split('.').filter(Boolean);
  if (parts.length === 0) return qualified;

  let tail = parts[parts.length - 1] ?? '';

  // Drop boilerplate suffix; if dropping it leaves nothing, fall back to
  // the parent segment.
  if (GENERIC_SUFFIX.test(tail) && parts.length >= 2) {
    const parent = parts[parts.length - 2] ?? '';
    if (parent) tail = parent;
  }

  if (!tail) return qualified;

  const words = splitSnake(tail).map(expandWord);
  if (words.length === 0) return qualified;

  // Insert spaces between camelCase boundaries inside each word.
  const expanded = words.flatMap((w) => w.replace(/([a-z])([A-Z])/g, '$1 $2').split(' '));

  const phrase = expanded.join(' ').replace(/\s+/g, ' ').trim();
  return sentenceCase(phrase);
}
