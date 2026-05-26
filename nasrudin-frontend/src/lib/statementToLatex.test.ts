import { describe, expect, it } from 'vitest';
import { statementToLatex } from './statementToLatex';

describe('statementToLatex', () => {
  it('returns empty for empty input', () => {
    expect(statementToLatex('')).toEqual({ latex: '', complete: false });
    expect(statementToLatex('   ')).toEqual({ latex: '', complete: false });
  });

  it('renders Π-binders as ∀-quantifiers when the var is used', () => {
    // Body `(@ v:Foo v:d)` references d, so this is genuine ∀d. Body for an
    // unused d would collapse to an arrow — see the next test.
    const { latex } = statementToLatex('(pi d v:Nat (@ v:Foo v:d))');
    expect(latex).toContain('\\forall');
    expect(latex).toContain('d : \\mathbb{N}');
  });

  it('renders unused Π as → arrow', () => {
    const { latex } = statementToLatex('(pi x v:Nat v:Real)');
    // `x` is not used in body → render as A → B, not as ∀.
    expect(latex).toBe('\\mathbb{N} \\to \\mathbb{R}');
  });

  it('renders equality', () => {
    const { latex } = statementToLatex('(= n:1 n:1)');
    expect(latex).toBe('1 = 1');
  });

  it('renders iff', () => {
    const { latex } = statementToLatex('(<-> v:True v:True)');
    expect(latex).toContain('\\iff');
  });

  it('renders ordered comparisons', () => {
    expect(statementToLatex('(< n:1 n:2)').latex).toBe('1 < 2');
    expect(statementToLatex('(<= n:1 n:1)').latex).toBe('1 \\leq 1');
    expect(statementToLatex('(>= n:2 n:1)').latex).toBe('2 \\geq 1');
  });

  it('renders arithmetic operators', () => {
    expect(statementToLatex('(+ n:1 n:2)').latex).toBe('1 + 2');
    expect(statementToLatex('(* n:2 n:3)').latex).toBe('2 \\cdot 3');
  });

  it('renders self-multiplication as square', () => {
    const { latex } = statementToLatex(
      '(* v:Lorentz.Vector.timeComponent v:Lorentz.Vector.timeComponent)',
    );
    expect(latex).toContain('^2');
  });

  it('renders E = m c^2 from the canonical S-expr the GA emits', () => {
    // The platform-default queue's `E = m * c^2` hunch produces this
    // canonical statement when a chain matches. Keep this rendering
    // human-readable in the corpus row + the theorem detail page:
    // the user shouldn't see `(= v:E (* v:m (^ c:c n:2)))` in a UI.
    // c:c is the PhysConst shorthand the test uses; production uses
    // c:SpeedOfLight — both must render. Test both.
    for (const c of ['c:c', 'c:SpeedOfLight']) {
      const r = statementToLatex(`(= v:E (* v:m (^ ${c} n:2)))`);
      expect(r.latex).toContain('E');
      expect(r.latex).toContain('=');
      expect(r.latex).toContain('m');
      expect(r.latex).toMatch(/\^[\s{]*2/);
    }
  });

  it('flattens curried applications', () => {
    // Single-letter idents skip \mathit (KaTeX italicises them by default).
    const { latex } = statementToLatex('(@ (@ v:Foo.f v:a) v:b)');
    expect(latex).toBe('f(a,\\, b)');
  });

  it('uses \\mathit for multi-letter idents', () => {
    const { latex } = statementToLatex('(@ v:Foo.helper v:thing)');
    expect(latex).toContain('\\mathit{helper}');
    expect(latex).toContain('\\mathit{thing}');
  });

  it('renders inner product as ⟨a,b⟩', () => {
    const { latex } = statementToLatex('(@ (@ (@ v:Inner.inner v:Real) v:a) v:b)');
    expect(latex).toContain('\\langle');
    expect(latex).toContain('\\rangle');
    expect(latex).not.toContain('Real'); // type witness stripped
  });

  it('renders membership as ∈', () => {
    const { latex } = statementToLatex('(@ (@ v:Membership.mem v:T) v:x)');
    expect(latex).toContain('\\in');
  });

  it('renders the timelike_time_dominates_space theorem', () => {
    const src =
      '(pi d v:Nat (pi v (@ v:Lorentz.Vector v:d) (-> (= (@ v:Lorentz.Vector.causalCharacter v:v) v:Lorentz.Vector.CausalCharacter.timeLike) (< (@ (@ (@ v:Inner.inner v:Real) (@ v:Lorentz.Vector.spatialPart v:v)) (@ v:Lorentz.Vector.spatialPart v:v)) (* (@ v:Lorentz.Vector.timeComponent v:v) (@ v:Lorentz.Vector.timeComponent v:v))))))';
    const { latex } = statementToLatex(src);
    // Should contain a forall over d, v, an arrow (the antecedent), an
    // inner product, a less-than, and a square via self-multiplication.
    expect(latex).toContain('\\forall');
    expect(latex).toContain('d : \\mathbb{N}');
    expect(latex).toContain('\\to');
    expect(latex).toContain('\\langle');
    expect(latex).toContain('<');
    expect(latex).toContain('^2');
  });

  it('renders the FourTree mem_iff_mem_toMultiset theorem', () => {
    const src =
      '(pi α1 v:<sort> (pi α2 v:<sort> (pi α3 v:<sort> (pi α4 v:<sort> (pi T (@ (@ (@ (@ v:PhysLean.FourTree v:α1) v:α2) v:α3) v:α4) (pi x (@ (@ v:Prod v:α1) (@ (@ v:Prod v:α2) (@ (@ v:Prod v:α3) v:α4))) (<-> (@ (@ v:Membership.mem v:T) v:x) (@ (@ v:Membership.mem (@ v:PhysLean.FourTree.toMultiset v:T)) v:x))))))))';
    const { latex } = statementToLatex(src);
    expect(latex).toContain('\\forall');
    expect(latex).toContain('\\iff');
    expect(latex).toContain('\\in');
  });

  it('renders Real type as ℝ', () => {
    const { latex } = statementToLatex('v:Real');
    expect(latex).toBe('\\mathbb{R}');
  });

  it('hides hygenic instance binders', () => {
    const src = '(pi inst._@.PhysLean.X.123._hygCtx._hyg.9 (@ v:DecidableRel v:le1) v:Real)';
    const { latex, complete } = statementToLatex(src);
    // The hygenic binder should not leak into the output.
    expect(latex).not.toContain('_hyg');
    expect(latex).not.toContain('inst._');
    // But we flag the rendering as incomplete since we dropped a binder.
    expect(complete).toBe(false);
  });

  it('returns complete:false for un-parseable input', () => {
    expect(statementToLatex('(((').complete).toBe(false);
    expect(statementToLatex('))').complete).toBe(false);
  });

  it('survives an unknown head without throwing', () => {
    const { latex } = statementToLatex('(weird-head v:a v:b)');
    expect(latex).toContain('?');
  });
});
