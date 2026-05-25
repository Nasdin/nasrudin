import { Math as MathExpr } from '~/lib/katex';
import {
  type StatementChunk,
  statementToSegments,
} from '~/lib/statementToLatex';

interface WrappedStatementProps {
  /** Prefer the server-side `latex` when populated; otherwise we parse the
   *  prefix-form `canonical_statement` ourselves. */
  serverLatex: string | null;
  /** Prefix-form Lean kernel expression (the AST string). */
  canonical: string;
  /** Visual size class. Theorem-page hero uses `'big'`; landing-page
   *  Live-card and corpus rows use `'inline'`. */
  size?: 'big' | 'inline';
}

// Renders a theorem statement that can wrap to multiple lines.
//
// The naive approach — one giant `<MathExpr block>` — produces a single
// `display: inline-block` element that the browser refuses to break, so
// long ∀-chained statements overflow horizontally and clip past the right
// edge of the page. Instead we split the statement at Π-binders and
// top-level operators (`→`, `=`, `<`, …) into a sequence of small math
// chunks separated by plain text. Each math chunk renders as its own
// inline `<MathExpr>`; the plain-text connectors act as wrap points so
// the browser breaks the line naturally between chunks, just like
// wrapping a sentence with embedded inline math.
export function WrappedStatement({
  serverLatex,
  canonical,
  size = 'big',
}: WrappedStatementProps) {
  // If the server pre-computed a LaTeX string (GA-derived theorems do)
  // we honour it as one chunk; we still wrap it inside `WrappedStatement`
  // so the surrounding container can apply `white-space: normal` and
  // line-height consistent with the segmented path.
  const segments = serverLatex
    ? { chunks: [{ kind: 'math' as const, latex: serverLatex }], complete: true }
    : statementToSegments(canonical);

  if (segments.chunks.length === 0) return null;

  const className =
    size === 'big' ? 'wrapped-statement wrapped-statement-big'
                   : 'wrapped-statement wrapped-statement-inline';

  return (
    <div className={className}>
      {segments.chunks.map((c, i) => renderChunk(c, i))}
    </div>
  );
}

function renderChunk(chunk: StatementChunk, key: number) {
  if (chunk.kind === 'text') {
    return (
      <span key={key} className="wrapped-statement-sep">
        {chunk.text}
      </span>
    );
  }
  return (
    <span key={key} className="wrapped-statement-math">
      <MathExpr source={chunk.latex} />
    </span>
  );
}
