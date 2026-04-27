import { Link } from '@tanstack/react-router';

const NUMERALS = ['i', 'ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii', 'ix', 'x'];

function romanize(n: number): string {
  return NUMERALS[n - 1] ?? String(n);
}

export function LineageList({ parents }: { parents: string[] }) {
  if (parents.length === 0) {
    return <p style={{ color: 'var(--ink-500)' }}>This theorem has no parents — it's an axiom.</p>;
  }
  return (
    <ol className="lineage">
      {parents.map((id, i) => (
        <li key={id}>
          <span className="lineage-step">{romanize(i + 1)}.</span>
          <span>
            <Link to="/theorem/$id" params={{ id }} className="lineage-name">
              {id}
            </Link>
          </span>
        </li>
      ))}
    </ol>
  );
}
