// Service worker for nasrudin-frontend.
//
// Caching strategy:
//   - Hashed Vite assets at /assets/* are immutable (filename embeds a content
//     hash). They get cache-first with no expiry — old assets simply sit in
//     the cache unused after a deploy, and the browser quota policy reclaims
//     them. New deploys emit new hashed names; the SW happily fetches and
//     caches those on first reference.
//   - HTML (the SSR entry document) goes network-first, no cache fallback.
//     This means a deploy is reflected on the very next page load. Offline
//     access is NOT a goal for this app (it needs a live API anyway).
//   - All other paths (/api/*, /favicon.svg, /install.sh, /sw.js itself) are
//     not intercepted — the browser handles them normally.
//
// The SW only needs `VERSION` bumped if the *worker logic* itself changes.
// Routine deploys do not need a bump.
const VERSION = 1;
const ASSETS_CACHE = `nasrudin-assets-v${VERSION}`;

self.addEventListener('install', (event) => {
  // Skip the "waiting" state so the new SW activates immediately on next
  // navigation instead of waiting for every tab to close.
  event.waitUntil(self.skipWaiting());
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    (async () => {
      // Drop any caches from older SW versions.
      const keys = await caches.keys();
      await Promise.all(
        keys.filter((k) => k !== ASSETS_CACHE).map((k) => caches.delete(k)),
      );
      // Take control of pages that loaded before this SW activated.
      await self.clients.claim();
    })(),
  );
});

self.addEventListener('fetch', (event) => {
  const req = event.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (url.origin !== self.location.origin) return;
  // Only intercept hashed asset URLs. Everything else is left to the browser.
  if (!url.pathname.startsWith('/assets/')) return;

  event.respondWith(
    (async () => {
      const cache = await caches.open(ASSETS_CACHE);
      const hit = await cache.match(req);
      if (hit) return hit;
      const res = await fetch(req);
      // Only cache successful, basic (same-origin) responses.
      if (res.ok && res.type === 'basic') {
        // Clone before consumption — Response bodies are single-use streams.
        cache.put(req, res.clone()).catch(() => {});
      }
      return res;
    })(),
  );
});
