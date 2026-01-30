import { createFileRoute } from '@tanstack/react-router'
import { Activity, Beaker, Dna, ShieldCheck } from 'lucide-react'
import TheoremCard from '../components/TheoremCard'
import { mockStats, mockTheorems } from '../lib/mock-data'

export const Route = createFileRoute('/')({ component: Dashboard })

function Dashboard() {
  const stats = [
    {
      label: 'Total Theorems',
      value: mockStats.total_theorems.toLocaleString(),
      icon: Beaker,
      color: 'text-indigo-400',
    },
    {
      label: 'Rate (/sec)',
      value: `${mockStats.rate}/s`,
      icon: Activity,
      color: 'text-emerald-400',
    },
    {
      label: 'Generation',
      value: mockStats.generation.toLocaleString(),
      icon: Dna,
      color: 'text-amber-400',
    },
    {
      label: 'Verified',
      value: `${mockStats.verified_pct}%`,
      icon: ShieldCheck,
      color: 'text-cyan-400',
    },
  ]

  const recentTheorems = mockTheorems.slice(0, 4)

  return (
    <div className="p-8 max-w-6xl mx-auto">
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-zinc-100">Dashboard</h1>
        <p className="text-sm text-zinc-500 mt-1">
          Real-time overview of the genetic algorithm physics discovery engine
        </p>
      </div>

      <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-4 gap-4 mb-10">
        {stats.map((stat) => {
          const Icon = stat.icon
          return (
            <div
              key={stat.label}
              className="bg-zinc-900 border border-zinc-800 rounded-lg p-5"
            >
              <div className="flex items-center justify-between mb-3">
                <span className="text-xs font-medium text-zinc-500 uppercase tracking-wider">
                  {stat.label}
                </span>
                <Icon size={18} className={stat.color} />
              </div>
              <p className={`text-2xl font-bold ${stat.color}`}>{stat.value}</p>
            </div>
          )
        })}
      </div>

      <div>
        <h2 className="text-lg font-semibold text-zinc-200 mb-4">
          Recent Discoveries
        </h2>
        <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
          {recentTheorems.map((thm) => (
            <TheoremCard
              key={thm.id}
              latex={thm.latex}
              domain={thm.domain}
              depth={thm.depth}
              fitness={thm.fitness}
              generation={thm.generation}
            />
          ))}
        </div>
      </div>
    </div>
  )
}
