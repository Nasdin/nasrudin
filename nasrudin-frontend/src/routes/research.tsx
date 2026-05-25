import { createFileRoute, Outlet } from '@tanstack/react-router';

// Pathless layout for `/research` and `/research/$id`. Without an
// `<Outlet />` here, the nested route `/research/$id` cannot render —
// the router resolves the parent segment and finds no slot for the
// child. The actual `/research` landing page lives in
// `research.index.tsx`.
export const Route = createFileRoute('/research')({ loader: async () => null, component: ResearchLayout });

function ResearchLayout() {
  return <Outlet />;
}
