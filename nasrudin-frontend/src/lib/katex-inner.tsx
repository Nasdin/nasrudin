import katex from 'katex';
import 'katex/dist/katex.min.css';

interface MathProps {
  source: string;
  block?: boolean;
}

// biome-ignore lint/suspicious/noShadowRestrictedNames: canonical component name for rendered math; the global Math object is unrelated to JSX components.
export default function MathInner({ source, block = false }: MathProps) {
  const html = katex.renderToString(source, {
    throwOnError: false,
    displayMode: block,
    output: 'html',
  });
  // KaTeX produces deterministic, sanitised HTML from a math AST (no scripts,
  // no event handlers). Inputs come from curated content + trusted API responses.
  // biome-ignore lint/security/noDangerouslySetInnerHtml: KaTeX HTML is deterministic and sanitised from a math AST; inputs are curated/trusted.
  return <span dangerouslySetInnerHTML={{ __html: html }} />;
}
