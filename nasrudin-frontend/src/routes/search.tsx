import { createFileRoute, Outlet } from '@tanstack/react-router';

// Pathless layout for `/search` and `/search/concept`. Without an
// `<Outlet />` here, the nested route `/search/concept` (file
// `search.concept.tsx`) cannot render — the router resolves the parent
// segment and finds no slot for the child. The actual `/search`
// landing page now lives in `search.index.tsx`.
export const Route = createFileRoute('/search')({ loader: async () => null, component: SearchLayout });

function SearchLayout() {
  return <Outlet />;
}
