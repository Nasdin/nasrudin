import { createFileRoute, Outlet } from '@tanstack/react-router';

// Pathless layout for `/conjecture` and `/conjecture/$id`. Without an
// `<Outlet />` here, the nested route `/conjecture/$id` cannot render —
// the router resolves the parent segment and finds no slot for the
// child. The actual `/conjecture` landing page lives in
// `conjecture.index.tsx`.
export const Route = createFileRoute('/conjecture')({ loader: async () => null, component: ConjectureLayout });

function ConjectureLayout() {
  return <Outlet />;
}
