import { tanstackStart } from '@tanstack/react-start/plugin/vite';
import { defineConfig, type Plugin } from 'vite';
import tsconfigPaths from 'vite-tsconfig-paths';

/// Splits big vendor libs into their own chunks for the **client build only**.
/// SSR externalises these modules, so chunking them there crashes Rollup.
/// Using a plugin scoped to the `client` environment is the only way Vite
/// v7 + TanStack Start honour the boundary — top-level `build.rollupOptions`
/// leaks into the SSR phase regardless of `environments.client` overrides.
function clientChunkSplit(): Plugin {
  return {
    name: 'client-chunk-split',
    apply: 'build',
    applyToEnvironment(env) {
      return env.name === 'client';
    },
    config() {
      return {
        build: {
          rollupOptions: {
            output: {
              // KaTeX (259 KB, lazy-loaded) and Firebase get explicit
              // chunks for stable hashing. @tanstack/react-query carries
              // `"use client"` directives that crash Rollup's renderer
              // when manually chunked, so leave it to Vite's automatic
              // per-route splitting.
              manualChunks(id: string) {
                if (id.includes('node_modules/katex')) return 'katex';
                if (id.includes('node_modules/firebase')) return 'firebase';
                return;
              },
            },
          },
        },
      };
    },
  };
}

export default defineConfig({
  plugins: [
    tsconfigPaths(),
    // `tanstackStart` already runs the router generator + per-environment
    // code splitter internally (see start-plugin-core/vite/start-router-plugin).
    // Adding a standalone `tanstackRouter()` here makes two generators
    // race on routeTree.gen.ts ("File ... was modified by another process
    // during processing") and emits duplicate `const hot = import.meta.hot`
    // bindings on every route ("Duplicate declaration 'hot'").
    tanstackStart({
      server: { entry: './ssr.tsx' },
      client: { entry: './client.tsx' },
    }),
    clientChunkSplit(),
  ],
  server: { port: 3000 },
});
