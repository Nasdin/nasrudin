// Lean prefix-form canonical_statement → LaTeX.
//
// The corpus stores theorem statements as Lean's kernel expression tree
// serialised in prefix form, e.g.
//
//   (pi d v:Nat (pi v (@ v:Lorentz.Vector v:d)
//      (-> (= (@ v:Lorentz.Vector.causalCharacter v:v)
//             v:Lorentz.Vector.CausalCharacter.timeLike)
//          (< (@ (@ (@ v:Inner.inner v:Real)
//                   (@ v:Lorentz.Vector.spatialPart v:v))
//                (@ v:Lorentz.Vector.spatialPart v:v))
//             (* (@ v:Lorentz.Vector.timeComponent v:v)
//                (@ v:Lorentz.Vector.timeComponent v:v))))))
//
// Atoms: `v:Foo.bar` references a global constant, `n:42` is a Nat literal,
// `<sort>` is a Sort universe, bare identifiers are bound vars introduced by
// an enclosing `pi`/`lambda`. Application is curried — `(@ (@ f a) b)`
// applies `f` to `a` then `b`. Special head symbols (`pi`, `lambda`, `->`,
// `<->`, `=`, `<`, `>`, `<=`, `>=`, `*`, `+`, `-`, `/`) are recognised
// structurally; everything else is treated as a generic name.
//
// Output: a KaTeX-compatible LaTeX fragment, plus a `complete` flag that's
// false when we punted on a sub-expression (the caller can decide whether to
// show the raw AST as a "view kernel form" toggle). The goal is "good enough
// for a professor to scan in 5 seconds", not full fidelity to Lean's kernel.

export interface StatementLatex {
  latex: string;
  /** True if every node was rendered structurally; false when we fell back
   *  to a textual representation for some subtree. */
  complete: boolean;
}

type Node = { kind: 'atom'; value: string } | { kind: 'list'; head: string | null; items: Node[] };

// ─── Lexer ──────────────────────────────────────────────────────────────────
// Tokens are `(`, `)`, or a run of non-space, non-paren characters. Dotted
// names like `Foo.Bar.baz` and prefixed names like `v:Foo.bar` are a single
// token. Whitespace is delimiter-only.

function tokenize(src: string): string[] {
  const out: string[] = [];
  let i = 0;
  while (i < src.length) {
    const ch = src[i] ?? '';
    if (ch === '(' || ch === ')') {
      out.push(ch);
      i += 1;
      continue;
    }
    if (/\s/.test(ch)) {
      i += 1;
      continue;
    }
    let j = i;
    while (j < src.length) {
      const c = src[j] ?? '';
      if (c === '(' || c === ')' || /\s/.test(c)) break;
      j += 1;
    }
    out.push(src.slice(i, j));
    i = j;
  }
  return out;
}

// ─── Parser ─────────────────────────────────────────────────────────────────

function parse(tokens: string[]): { node: Node | null; complete: boolean } {
  let pos = 0;
  let complete = true;

  function next(): Node | null {
    if (pos >= tokens.length) {
      complete = false;
      return null;
    }
    const tok = tokens[pos] ?? '';
    if (tok === ')') {
      complete = false;
      return null;
    }
    if (tok === '(') {
      pos += 1;
      const items: Node[] = [];
      while (pos < tokens.length && tokens[pos] !== ')') {
        const child = next();
        if (child === null) return null;
        items.push(child);
      }
      if (tokens[pos] !== ')') {
        complete = false;
        return null;
      }
      pos += 1;
      const headNode = items[0];
      const head = headNode && headNode.kind === 'atom' ? headNode.value : null;
      return { kind: 'list', head, items };
    }
    pos += 1;
    return { kind: 'atom', value: tok };
  }

  const node = next();
  if (pos !== tokens.length) complete = false;
  return { node, complete };
}

// ─── Emitter ────────────────────────────────────────────────────────────────

// Last `.`-segment of a v:Foo.bar.baz reference — what we actually display.
function lastSegment(name: string): string {
  const i = name.lastIndexOf('.');
  return i === -1 ? name : name.slice(i + 1);
}

// Greek letters Lean accepts in identifiers — show literal char if it's the
// whole identifier, else strip to a safe ASCII label.
const ATOM_RENDER: Record<string, string> = {
  Real: '\\mathbb{R}',
  Complex: '\\mathbb{C}',
  Nat: '\\mathbb{N}',
  Int: '\\mathbb{Z}',
  Rat: '\\mathbb{Q}',
  Bool: '\\text{Bool}',
  Prop: '\\text{Prop}',
  Type: '\\text{Type}',
  True: '\\top',
  False: '\\bot',
};

// Last-segment overrides — physics-y identifiers we want to render as
// proper symbols.
const CONST_SYMBOL: Record<string, string> = {
  SpeedOfLight: 'c',
  PlanckConstant: 'h',
  ReducedPlanckConstant: '\\hbar',
  GravitationalConstant: 'G',
  BoltzmannConstant: 'k_B',
  VacuumPermittivity: '\\varepsilon_0',
  VacuumPermeability: '\\mu_0',
  ProperTime: '\\tau',
  causalCharacter: '\\text{causalCharacter}',
  spatialPart: '\\mathbf{v}_{\\text{spatial}}',
  timeComponent: 'v_t',
  toMultiset: '\\text{toMultiset}',
};

function escapeIdent(name: string): string {
  // KaTeX \text{} treats underscores literally but not as subscript — we'd
  // rather have `causalCharacter` render as text than as italic with broken
  // sub/sup. So wrap multi-letter identifiers in \mathit{} (italic math)
  // after replacing underscores with safe glyph.
  const safe = name.replace(/_/g, '\\_');
  if (name.length === 1) return safe;
  return `\\mathit{${safe}}`;
}

function renderAtom(value: string): string {
  // `v:Foo.Bar.baz` → constant reference; render the last segment.
  if (value.startsWith('v:')) {
    const inner = value.slice(2);
    if (inner === '<sort>') return '\\text{Sort}';
    if (ATOM_RENDER[inner]) return ATOM_RENDER[inner] as string;
    const last = lastSegment(inner);
    if (CONST_SYMBOL[last]) return CONST_SYMBOL[last] as string;
    if (ATOM_RENDER[last]) return ATOM_RENDER[last] as string;
    return escapeIdent(last);
  }
  // `n:42` → numeric literal.
  if (value.startsWith('n:')) return value.slice(2);
  // `<sort>` → universe.
  if (value === '<sort>') return '\\text{Sort}';
  // Plain bound variable.
  return escapeIdent(value);
}

// Walk curried applications back to the head and collect args, so
// `(@ (@ (@ f a) b) c)` returns `{ head: f, args: [a,b,c] }`.
function flattenApp(n: Node): { head: Node; args: Node[] } {
  let head: Node = n;
  const args: Node[] = [];
  while (head.kind === 'list' && head.head === '@' && head.items.length === 3) {
    const [, fn, arg] = head.items;
    if (!fn || !arg) break;
    args.unshift(arg);
    head = fn;
  }
  return { head, args };
}

function constLastSegment(n: Node): string | null {
  if (n.kind === 'atom' && n.value.startsWith('v:')) {
    return lastSegment(n.value.slice(2));
  }
  return null;
}

// Recognised infix/named operators rendered as proper math.
//
// Returns the LaTeX fragment if the head is one we special-case, otherwise
// null so the caller falls back to generic application rendering.
function renderOperator(head: Node, args: Node[], emit: (n: Node) => string): string | null {
  const name = constLastSegment(head);
  if (!name) return null;

  // `Inner.inner Real a b` → `\langle a, b \rangle`.
  // Inner.inner is curried as `(@ (@ (@ v:Inner.inner v:Real) a) b)`.
  if (name === 'inner' && args.length >= 3) {
    const a = args[args.length - 2];
    const b = args[args.length - 1];
    if (a && b) return `\\langle ${emit(a)},\\, ${emit(b)} \\rangle`;
  }

  // `Membership.mem a b` → `a \in b`. Lean curries it.
  if (name === 'mem' && args.length >= 2) {
    const a = args[args.length - 2];
    const b = args[args.length - 1];
    if (a && b) return `${emit(a)} \\in ${emit(b)}`;
  }

  // `HSMul.hSMul a b` → `a \cdot b`.
  if (name === 'hSMul' && args.length >= 2) {
    const a = args[args.length - 2];
    const b = args[args.length - 1];
    if (a && b) return `${emit(a)} \\cdot ${emit(b)}`;
  }

  // `DFunLike.coe f x` → `f(x)`.
  if (name === 'coe' && args.length >= 2) {
    const f = args[args.length - 2];
    const x = args[args.length - 1];
    if (f && x) return `${emit(f)}(${emit(x)})`;
  }

  return null;
}

// Collapse `(pi x T1 (pi y T1 (pi z T2 body)))` into
// `[ {names:[x,y], type:T1}, {names:[z], type:T2} ]` so we can group binders
// by repeated type — `∀ x, y : ℝ. ∀ z : ℕ. body`.
function collectBinders(
  n: Node,
  binderKind: 'pi' | 'lambda',
): { groups: { names: string[]; type: Node }[]; body: Node } {
  const groups: { names: string[]; type: Node }[] = [];
  let cur: Node = n;
  while (cur.kind === 'list' && cur.head === binderKind && cur.items.length === 4) {
    const [, name, type, body] = cur.items;
    if (!name || !type || !body || name.kind !== 'atom') break;
    const last = groups[groups.length - 1];
    if (last && nodeEq(last.type, type)) {
      last.names.push(name.value);
    } else {
      groups.push({ names: [name.value], type });
    }
    cur = body;
  }
  return { groups, body: cur };
}

function nodeEq(a: Node, b: Node): boolean {
  if (a.kind !== b.kind) return false;
  if (a.kind === 'atom' && b.kind === 'atom') return a.value === b.value;
  if (a.kind === 'list' && b.kind === 'list') {
    if (a.items.length !== b.items.length) return false;
    for (let i = 0; i < a.items.length; i++) {
      const ai = a.items[i];
      const bi = b.items[i];
      if (!ai || !bi || !nodeEq(ai, bi)) return false;
    }
    return true;
  }
  return false;
}

// Hygenic / instance binders Lean inserts that add no signal for the reader.
function isHygenic(name: string): boolean {
  return (
    name.startsWith('inst._@.') ||
    name.startsWith('inst.') ||
    name.includes('._hygCtx._hyg.') ||
    name.startsWith('_hyg.')
  );
}

interface Ctx {
  setIncomplete: () => void;
}

function emitNode(n: Node, ctx: Ctx): string {
  if (n.kind === 'atom') return renderAtom(n.value);

  // Quantifiers.
  if (n.head === 'pi' && n.items.length === 4) {
    const { groups, body } = collectBinders(n, 'pi');
    const cleaned = groups.filter((g) => !g.names.every(isHygenic));
    const dropped = groups.length - cleaned.length;
    if (dropped > 0) ctx.setIncomplete();

    // If only one group and its single var doesn't appear in the body —
    // it's actually a `->` arrow (Lean models `A → B` as `Π _ : A, B`).
    if (cleaned.length === 1) {
      const g0 = cleaned[0];
      if (g0 && g0.names.length === 1) {
        const onlyName = g0.names[0];
        if (onlyName && !nameAppearsIn(body, onlyName)) {
          return `${emitNode(g0.type, ctx)} \\to ${emitNode(body, ctx)}`;
        }
      }
    }

    const binders = cleaned
      .map((g) => {
        const names = g.names.map(escapeIdent).join(',\\, ');
        return `${names} : ${emitNode(g.type, ctx)}`;
      })
      .join(',\\ ');
    if (!binders) return emitNode(body, ctx);
    return `\\forall ${binders}.\\ ${emitNode(body, ctx)}`;
  }

  if (n.head === 'lambda' && n.items.length === 4) {
    const { groups, body } = collectBinders(n, 'lambda');
    const cleaned = groups.filter((g) => !g.names.every(isHygenic));
    const dropped = groups.length - cleaned.length;
    if (dropped > 0) ctx.setIncomplete();
    const binders = cleaned.map((g) => g.names.map(escapeIdent).join(',\\, ')).join(',\\, ');
    if (!binders) return emitNode(body, ctx);
    return `\\lambda ${binders}.\\ ${emitNode(body, ctx)}`;
  }

  // Built-in binary symbols (don't go through `@` curry).
  if (n.head === '->' && n.items.length === 3) {
    const a = n.items[1];
    const b = n.items[2];
    if (a && b) return `${emitNode(a, ctx)} \\to ${emitNode(b, ctx)}`;
  }
  if (n.head === '<->' && n.items.length === 3) {
    const a = n.items[1];
    const b = n.items[2];
    if (a && b) return `${emitNode(a, ctx)} \\iff ${emitNode(b, ctx)}`;
  }
  if (n.head === '=' && n.items.length === 3) {
    const a = n.items[1];
    const b = n.items[2];
    if (a && b) return `${emitNode(a, ctx)} = ${emitNode(b, ctx)}`;
  }
  if (
    (n.head === '<' || n.head === '>' || n.head === '<=' || n.head === '>=') &&
    n.items.length === 3
  ) {
    const op = n.head === '<=' ? '\\leq' : n.head === '>=' ? '\\geq' : n.head;
    const a = n.items[1];
    const b = n.items[2];
    if (a && b) return `${emitNode(a, ctx)} ${op} ${emitNode(b, ctx)}`;
  }
  if (
    (n.head === '+' || n.head === '-' || n.head === '*' || n.head === '/') &&
    n.items.length === 3
  ) {
    const a = n.items[1];
    const b = n.items[2];
    if (a && b) {
      // `(* a a)` → `a^2` if both sides are literally identical (common in
      // squared-norm-style statements).
      if (n.head === '*' && nodeEq(a, b)) {
        return `${emitNode(a, ctx)}^2`;
      }
      const op = n.head === '*' ? '\\cdot' : n.head === '/' ? '/' : n.head;
      return `${emitNode(a, ctx)} ${op} ${emitNode(b, ctx)}`;
    }
  }

  // Curried application.
  if (n.head === '@' && n.items.length === 3) {
    const { head, args } = flattenApp(n);

    // Operator-style rewrites first (inner product, membership, …).
    const op = renderOperator(head, args, (sub) => emitNode(sub, ctx));
    if (op !== null) return op;

    // Generic application: `f(a, b, c)`. Strip implicit "type-witness"
    // first args (single uppercase identifiers like `Real` / `Nat`) when
    // the head is a function-style constant — those are typeclass type
    // arguments that we don't want cluttering the display.
    const headLatex = emitNode(head, ctx);
    const visibleArgs = stripTypeWitnesses(head, args);
    if (visibleArgs.length === 0) return headLatex;
    const renderedArgs = visibleArgs.map((a) => emitNode(a, ctx)).join(',\\, ');
    return `${headLatex}(${renderedArgs})`;
  }

  // Unrecognised list shape — fall back to a textual stub.
  ctx.setIncomplete();
  return `\\mathtt{?}`;
}

// Drop leading args of an application that look like implicit typeclass
// resolution rather than meaningful values. e.g. for `Inner.inner Real a b`
// the `Real` is the inner-product space type, not a value.
function stripTypeWitnesses(head: Node, args: Node[]): Node[] {
  if (head.kind !== 'atom' || !head.value.startsWith('v:')) return args;
  const name = lastSegment(head.value.slice(2));
  // Conservative list: heads we know take an implicit type witness as the
  // first explicit arg in their Lean kernel signature.
  const STRIP_FIRST: Record<string, true> = {
    inner: true,
    mem: true,
    coe: true,
  };
  if (STRIP_FIRST[name] && args.length > 1) {
    const a = args[0];
    if (a && a.kind === 'atom' && a.value.startsWith('v:')) {
      return args.slice(1);
    }
  }
  return args;
}

function nameAppearsIn(n: Node, name: string): boolean {
  // Bound variables show up two ways in Lean's serialised AST: as the bare
  // binder name in the body of a `(lambda x …)` body where x is referenced
  // directly, and (more commonly) as `v:x` when the body of a Π references
  // a parameter introduced by an outer Π. Match both.
  if (n.kind === 'atom') return n.value === name || n.value === `v:${name}`;
  return n.items.some((c) => nameAppearsIn(c, name));
}

// ─── Public entry ───────────────────────────────────────────────────────────

// ─── Segmented (wrappable) statement renderer ───────────────────────────────
//
// `statementToLatex` returns a single LaTeX string. KaTeX renders that string
// as one `display: inline-block` element which the browser does not wrap, so
// long ∀-chained statements overflow the page horizontally. To get genuine
// word-wrapping we instead emit the statement as an alternating sequence of
// math chunks (each a tiny KaTeX-renderable LaTeX string) and plain-text
// connectors. The renderer drops each math chunk into its own `<MathExpr>`
// and the browser wraps between them at the connector text exactly the same
// way it wraps a sentence.

export type StatementChunk =
  | { kind: 'math'; latex: string }
  | { kind: 'text'; text: string };

export interface StatementSegments {
  chunks: StatementChunk[];
  /** Same semantics as `StatementLatex.complete`. */
  complete: boolean;
}

function chunkAtom(value: string): StatementChunk {
  return { kind: 'math', latex: renderAtom(value) };
}

function emitChunks(n: Node, ctx: Ctx, out: StatementChunk[]) {
  // Π-chain: emit each binder group as its own math chunk, with comma /
  // space text between so the browser has a wrap point. The trailing body
  // recursively emits its own chunks.
  if (n.kind === 'list' && n.head === 'pi' && n.items.length === 4) {
    const { groups, body } = collectBinders(n, 'pi');
    const cleaned = groups.filter((g) => !g.names.every(isHygenic));
    const dropped = groups.length - cleaned.length;
    if (dropped > 0) ctx.setIncomplete();

    // Unused single binder → render as `A → B` directly.
    if (cleaned.length === 1) {
      const g0 = cleaned[0];
      if (g0 && g0.names.length === 1) {
        const onlyName = g0.names[0];
        if (onlyName && !nameAppearsIn(body, onlyName)) {
          out.push({ kind: 'math', latex: emitNode(g0.type, ctx) });
          out.push({ kind: 'text', text: ' → ' });
          emitChunks(body, ctx, out);
          return;
        }
      }
    }

    if (cleaned.length === 0) {
      emitChunks(body, ctx, out);
      return;
    }

    cleaned.forEach((g, i) => {
      const names = g.names.map(escapeIdent).join(',\\, ');
      const piece = `\\forall\\, ${names} : ${emitNode(g.type, ctx)}`;
      out.push({ kind: 'math', latex: piece });
      // Comma between binder groups, period before the body.
      out.push({
        kind: 'text',
        text: i + 1 < cleaned.length ? ', ' : '. ',
      });
    });
    emitChunks(body, ctx, out);
    return;
  }

  // Top-level arrow / iff / equality / comparison: split around the
  // operator so the two sides become independent chunks with a text
  // connector. These are the most common natural wrap points in formal
  // statements ("antecedent → consequent", "lhs = rhs").
  if (n.kind === 'list' && n.items.length === 3) {
    const op = n.head;
    const left = n.items[1];
    const right = n.items[2];
    if (left && right) {
      if (op === '->') {
        emitChunks(left, ctx, out);
        out.push({ kind: 'text', text: ' → ' });
        emitChunks(right, ctx, out);
        return;
      }
      if (op === '<->') {
        emitChunks(left, ctx, out);
        out.push({ kind: 'text', text: ' ⇔ ' });
        emitChunks(right, ctx, out);
        return;
      }
      if (op === '=' || op === '<' || op === '>' || op === '<=' || op === '>=') {
        const sym =
          op === '<=' ? ' ≤ ' : op === '>=' ? ' ≥ ' : ` ${op} `;
        emitChunks(left, ctx, out);
        out.push({ kind: 'text', text: sym });
        emitChunks(right, ctx, out);
        return;
      }
    }
  }

  // Bare atom — wrap as a single math chunk.
  if (n.kind === 'atom') {
    out.push(chunkAtom(n.value));
    return;
  }

  // Fall-through: render the whole subtree as one math chunk. It won't
  // wrap internally, but the surrounding text connectors above will keep
  // it from being the entire statement.
  out.push({ kind: 'math', latex: emitNode(n, ctx) });
}

export function statementToSegments(canonical: string): StatementSegments {
  if (!canonical || !canonical.trim()) {
    return { chunks: [], complete: false };
  }
  const tokens = tokenize(canonical);
  const { node, complete: parseOk } = parse(tokens);
  if (!node) return { chunks: [], complete: false };
  let renderOk = true;
  const ctx: Ctx = {
    setIncomplete: () => {
      renderOk = false;
    },
  };
  const chunks: StatementChunk[] = [];
  try {
    emitChunks(node, ctx, chunks);
  } catch {
    return { chunks: [], complete: false };
  }
  return { chunks, complete: parseOk && renderOk };
}

/** A single upstream constant referenced inside a theorem's canonical
 *  statement — e.g. the timelike-dominance theorem references
 *  `Lorentz.Vector`, `Lorentz.Vector.causalCharacter`,
 *  `Inner.inner`, etc. The TrustPanel uses this to render "this
 *  theorem is built atop these named upstream definitions" instead of
 *  the useless list of SHA hashes from the `parents` field. */
export interface UpstreamRef {
  /** The full Lean qualifier as it appears in the AST, e.g.
   *  `Lorentz.Vector.causalCharacter`. */
  qualifier: string;
  /** The display name (last `.`-segment, with snake_case kept). */
  name: string;
  /** Everything before the last segment, dot-joined. Empty when the
   *  reference has no namespace (e.g. `Real`, `Nat`). */
  namespace: string;
}

// Identifiers we don't surface — Lean type universes (`Type`, `Sort`,
// `Prop`), Mathlib's foundational primitives, and a handful of always-
// present helper traits that ship with virtually every statement and
// add zero signal to the user.
const REF_IGNORE = new Set([
  'Sort',
  'Type',
  'Prop',
  'Nat',
  'Int',
  'Real',
  'Complex',
  'Rat',
  'Bool',
  'True',
  'False',
  // `<sort>` token from the serialiser.
  '<sort>',
]);

// Patterns that indicate the qualifier is internal Lean machinery rather
// than a user-meaningful dependency. Auto-generated proof helpers
// (`_proof_1`, `_proof_2`), hygenic names from macro expansion
// (`._hygCtx._hyg.<n>`), Lean's `_internal` namespace, and the empty
// `_proof_N` last-segment all leak into the AST but add zero signal —
// hiding them keeps the "Built from" panel focused on names a reader
// actually wants to click.
const NOISE_PATTERNS: RegExp[] = [
  /^_proof_\d+$/,
  /^_proof$/,
  /^_internal(\.|$)/,
  /^.*\._hygCtx\._hyg\.\d+/,
  /^.*\._hyg\.\d+$/,
  /^.*\._@\./, // internal anonymous namespace markers
  /^.*\.proof_\d+$/,
  /^inst\./,
  /^inst$/,
  /^inst_\d+$/,
];

function isNoiseQualifier(inner: string, name: string): boolean {
  for (const re of NOISE_PATTERNS) {
    if (re.test(inner) || re.test(name)) return true;
  }
  return false;
}

function walkRefs(n: Node, out: Map<string, UpstreamRef>) {
  if (n.kind === 'atom') {
    if (n.value.startsWith('v:')) {
      const inner = n.value.slice(2);
      const dot = inner.lastIndexOf('.');
      // Only include references that have a real namespace prefix —
      // bare bound-variable references (`v:d`, `v:x`) come from Π/λ
      // binders and aren't dependencies on upstream constants.
      if (dot > 0) {
        const namespace = inner.slice(0, dot);
        const name = inner.slice(dot + 1);
        if (
          !REF_IGNORE.has(inner) &&
          !REF_IGNORE.has(name) &&
          !isNoiseQualifier(inner, name)
        ) {
          out.set(inner, { qualifier: inner, name, namespace });
        }
      }
    }
    return;
  }
  for (const c of n.items) walkRefs(c, out);
}

/** Extract every namespaced upstream constant referenced inside the
 *  canonical statement. De-duplicated and sorted by qualifier so the
 *  TrustPanel's display order is stable. */
export function collectUpstreamRefs(canonical: string): UpstreamRef[] {
  if (!canonical || !canonical.trim()) return [];
  const tokens = tokenize(canonical);
  const { node } = parse(tokens);
  if (!node) return [];
  const out = new Map<string, UpstreamRef>();
  walkRefs(node, out);
  return [...out.values()].sort((a, b) => a.qualifier.localeCompare(b.qualifier));
}

export function statementToLatex(canonical: string): StatementLatex {
  if (!canonical || !canonical.trim()) {
    return { latex: '', complete: false };
  }
  const tokens = tokenize(canonical);
  const { node, complete: parseOk } = parse(tokens);
  if (!node) return { latex: '', complete: false };
  let renderOk = true;
  const ctx: Ctx = {
    setIncomplete: () => {
      renderOk = false;
    },
  };
  let latex: string;
  try {
    latex = emitNode(node, ctx);
  } catch {
    return { latex: '', complete: false };
  }
  return { latex, complete: parseOk && renderOk };
}
