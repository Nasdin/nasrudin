import { Link } from '@tanstack/react-router'
import 'katex/dist/katex.min.css'
import { BlockMath } from 'react-katex'
import DomainBadge from './DomainBadge'

interface TheoremCardProps {
  id: string
  latex: string
  domain: string
  depth: number
  fitness?: number
  generation?: number
}

export default function TheoremCard({
  id,
  latex,
  domain,
  depth,
  fitness,
  generation,
}: TheoremCardProps) {
  return (
    <Link
      to="/theorem/$theoremId"
      params={{ theoremId: id }}
      className="block bg-white border border-slate-200 rounded-lg p-4 hover:border-slate-300 hover:shadow-sm transition-all"
    >
      <div className="mb-3 overflow-x-auto">
        <BlockMath math={latex} />
      </div>
      <div className="flex items-center justify-between flex-wrap gap-2">
        <DomainBadge domain={domain} />
        <div className="flex items-center gap-3 text-xs text-slate-500">
          <span>depth {depth}</span>
          {fitness !== undefined && (
            <span>fitness {(fitness * 100).toFixed(1)}%</span>
          )}
          {generation !== undefined && <span>gen {generation}</span>}
        </div>
      </div>
    </Link>
  )
}
