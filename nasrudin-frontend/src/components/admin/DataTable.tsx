/**
 * Minimal generic table for the admin panel. Server-paginated; rendering
 * is the caller's job via Column.render. Deliberately bare-bones — sort
 * + filter UI live in the parent route since they drive URL state.
 */

import type { ReactNode } from 'react';

export interface Column<R> {
  key: keyof R & string;
  header: string;
  render?: (row: R) => ReactNode;
}

interface Props<R> {
  columns: Column<R>[];
  rows: R[];
  emptyMessage?: string;
}

const tableStyle: React.CSSProperties = { width: '100%', borderCollapse: 'collapse' };
const thStyle: React.CSSProperties = {
  textAlign: 'left',
  borderBottom: '1px solid var(--paper-300)',
  padding: '8px',
};
const trStyle: React.CSSProperties = { borderBottom: '1px solid var(--paper-200)' };
const tdStyle: React.CSSProperties = { padding: '8px', verticalAlign: 'top' };

export default function DataTable<R>({
  columns,
  rows,
  emptyMessage = 'No rows.',
}: Props<R>) {
  if (rows.length === 0) {
    return <p className="admin-empty">{emptyMessage}</p>;
  }
  return (
    <table className="admin-table" style={tableStyle}>
      <thead>
        <tr>
          {columns.map((c) => (
            <th key={c.key} style={thStyle}>
              {c.header}
            </th>
          ))}
        </tr>
      </thead>
      <tbody>
        {rows.map((r, i) => (
          <tr key={i} style={trStyle}>
            {columns.map((c) => (
              <td key={c.key} style={tdStyle}>
                {c.render ? c.render(r) : String((r as Record<string, unknown>)[c.key] ?? '')}
              </td>
            ))}
          </tr>
        ))}
      </tbody>
    </table>
  );
}
