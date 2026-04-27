import { createFileRoute } from '@tanstack/react-router';

export const Route = createFileRoute('/')({ component: Index });

function Index() {
  return (
    <div className="page" style={{ padding: 64 }}>
      nasrudin-frontend up
    </div>
  );
}
