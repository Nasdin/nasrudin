import { StartClient } from '@tanstack/react-start/client';
import { StrictMode, startTransition } from 'react';
import { hydrateRoot } from 'react-dom/client';

startTransition(() => {
  hydrateRoot(
    document,
    <StrictMode>
      <StartClient />
    </StrictMode>,
  );
});

// Register the service worker after hydration. Caches Vite's hashed
// /assets/* with cache-first — repeat visits skip the network for
// the big chunks (KaTeX 259 KB, firebase 102 KB, main 362 KB).
// HTML stays network-first inside the SW so deploys propagate instantly.
if (typeof window !== 'undefined' && 'serviceWorker' in navigator) {
  window.addEventListener('load', () => {
    navigator.serviceWorker.register('/sw.js').catch(() => {
      // Registration can fail on insecure contexts (http://) or if the
      // browser blocks SW for the origin. The app works without it.
    });
  });
}
