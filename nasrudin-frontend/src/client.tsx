import { StartClient } from '@tanstack/react-start/client';
import { StrictMode, startTransition } from 'react';
import { hydrateRoot } from 'react-dom/client';

// When a deploy lands while a tab is open, hash-suffixed Vite chunks the
// in-memory bundle references stop existing on the server. The next
// dynamic import (e.g. clicking "Donate" → import("./sponsor-X.js"))
// fails with "Failed to fetch dynamically imported module" and the
// router shows the catch-all error screen. Vite emits a non-bubbling
// `vite:preloadError` for this exact case — handling it as a soft
// reload picks up the new index.html and its current chunk hashes.
//
// The session-storage guard prevents an infinite reload loop if the
// failure is caused by something other than stale chunks (CDN outage,
// bad network, etc.) — we reload at most once per browser session, then
// surface the error normally.
if (typeof window !== 'undefined') {
  window.addEventListener('vite:preloadError', (event) => {
    event.preventDefault();
    const RELOAD_KEY = '__nasrudin_chunk_reload';
    if (sessionStorage.getItem(RELOAD_KEY) === '1') return;
    sessionStorage.setItem(RELOAD_KEY, '1');
    window.location.reload();
  });
  // Successful navigation clears the guard so a *future* stale-bundle
  // event in the same session (long-lived tab through two deploys)
  // gets one fresh reload.
  window.addEventListener('load', () => {
    sessionStorage.removeItem('__nasrudin_chunk_reload');
  });
}

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
