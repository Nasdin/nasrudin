import { createFileRoute } from '@tanstack/react-router'
import 'katex/dist/katex.min.css'
import { BlockMath } from 'react-katex'
import DomainBadge from '../components/DomainBadge'
import { mockTimelineEntries } from '../lib/mock-data'

export const Route = createFileRoute('/timeline')({ component: TimelinePage })

function formatTime(iso: string): string {
  const date = new Date(iso)
  return date.toLocaleTimeString('en-US', {
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    hour12: false,
  })
}

function formatDate(iso: string): string {
  const date = new Date(iso)
  return date.toLocaleDateString('en-US', {
    year: 'numeric',
    month: 'short',
    day: 'numeric',
  })
}

const operatorColors: Record<string, string> = {
  Crossover: 'bg-indigo-500/20 text-indigo-400 border-indigo-500/30',
  Mutation: 'bg-emerald-500/20 text-emerald-400 border-emerald-500/30',
  Selection: 'bg-amber-500/20 text-amber-400 border-amber-500/30',
}

function TimelinePage() {
  return (
    <div className="p-8 max-w-4xl mx-auto">
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-zinc-100">Timeline</h1>
        <p className="text-sm text-zinc-500 mt-1">
          Chronological record of discovered theorems
        </p>
      </div>

      <div className="relative">
        <div className="absolute left-4 top-0 bottom-0 w-px bg-zinc-800" />

        <div className="space-y-6">
          {mockTimelineEntries.map((entry) => {
            const opColor =
              operatorColors[entry.operator] ??
              'bg-zinc-500/20 text-zinc-400 border-zinc-500/30'

            return (
              <div key={entry.id} className="relative pl-12">
                <div className="absolute left-2.5 top-5 w-3 h-3 rounded-full bg-indigo-500 border-2 border-zinc-950" />

                <div className="bg-zinc-900 border border-zinc-800 rounded-lg p-4 hover:border-zinc-700 transition-colors">
                  <div className="flex items-center justify-between mb-3 flex-wrap gap-2">
                    <div className="flex items-center gap-2 text-xs text-zinc-500">
                      <span>{formatDate(entry.timestamp)}</span>
                      <span className="text-zinc-700">|</span>
                      <span className="font-mono">
                        {formatTime(entry.timestamp)}
                      </span>
                    </div>
                    <div className="flex items-center gap-2">
                      <span
                        className={`inline-flex items-center px-2 py-0.5 rounded-full text-xs font-medium border ${opColor}`}
                      >
                        {entry.operator}
                      </span>
                      <DomainBadge domain={entry.theorem.domain} />
                    </div>
                  </div>
                  <div className="overflow-x-auto">
                    <BlockMath math={entry.theorem.latex} />
                  </div>
                  <div className="mt-2 flex items-center gap-3 text-xs text-zinc-500">
                    <span>depth {entry.theorem.depth}</span>
                    <span>
                      fitness {(entry.theorem.fitness * 100).toFixed(1)}%
                    </span>
                    <span>gen {entry.theorem.generation}</span>
                  </div>
                </div>
              </div>
            )
          })}
        </div>
      </div>
    </div>
  )
}
