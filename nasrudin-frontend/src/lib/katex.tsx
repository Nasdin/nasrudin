import { lazy, Suspense } from 'react';

interface MathProps {
  source: string;
  block?: boolean;
}

// Lazy-loads the KaTeX bundle (~259 KB JS + CSS) only when the first math
// expression actually renders. Routes that never show LaTeX never pay the cost.
const MathInner = lazy(() => import('./katex-inner'));

// biome-ignore lint/suspicious/noShadowRestrictedNames: canonical component name for rendered math; the global Math object is unrelated to JSX components.
export function Math({ source, block = false }: MathProps) {
  return (
    <Suspense fallback={<code>{source}</code>}>
      <MathInner source={source} block={block} />
    </Suspense>
  );
}
