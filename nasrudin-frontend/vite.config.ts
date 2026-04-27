import { tanstackStart } from '@tanstack/react-start/plugin/vite';
import { tanstackRouter } from '@tanstack/router-plugin/vite';
import { defineConfig } from 'vite';
import tsconfigPaths from 'vite-tsconfig-paths';

export default defineConfig({
  plugins: [
    tsconfigPaths(),
    tanstackRouter({ target: 'react', autoCodeSplitting: true }),
    tanstackStart({
      // TanStack Start v1.157 expects `src/server.ts` by default for the SSR entry
      // and `src/client.ts` for the client entry. The plan names ours `ssr.tsx`
      // and `client.tsx`, so point the plugin at those explicit paths.
      server: { entry: './ssr.tsx' },
      client: { entry: './client.tsx' },
    }),
  ],
  server: { port: 3000 },
});
