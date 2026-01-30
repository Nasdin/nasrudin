import { createFileRoute } from '@tanstack/react-router'
import {
  Atom,
  Flame,
  Magnet,
  Orbit,
  Rocket,
  Zap,
} from 'lucide-react'
import DomainBadge from '../../components/DomainBadge'
import { domainDescriptions } from '../../lib/mock-data'

export const Route = createFileRoute('/domains/')({ component: DomainsPage })

const domainIcons: Record<string, React.ElementType> = {
  'Classical Mechanics': Rocket,
  Electromagnetism: Zap,
  'Special Relativity': Orbit,
  'General Relativity': Magnet,
  'Quantum Mechanics': Atom,
  Thermodynamics: Flame,
}

const domainIconColors: Record<string, string> = {
  'Classical Mechanics': 'text-blue-400',
  Electromagnetism: 'text-yellow-400',
  'Special Relativity': 'text-purple-400',
  'General Relativity': 'text-red-400',
  'Quantum Mechanics': 'text-green-400',
  Thermodynamics: 'text-orange-400',
}

function DomainsPage() {
  const domains = Object.entries(domainDescriptions)

  return (
    <div className="p-8 max-w-5xl mx-auto">
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-zinc-100">Domains</h1>
        <p className="text-sm text-zinc-500 mt-1">
          Physics domains explored by the genetic algorithm engine
        </p>
      </div>

      <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
        {domains.map(([name, info]) => {
          const Icon = domainIcons[name] ?? Atom
          const iconColor = domainIconColors[name] ?? 'text-zinc-400'

          return (
            <div
              key={name}
              className="bg-zinc-900 border border-zinc-800 rounded-lg p-5 hover:border-zinc-700 transition-colors"
            >
              <div className="flex items-start justify-between mb-4">
                <Icon size={28} className={iconColor} />
                <DomainBadge domain={name} />
              </div>
              <h3 className="text-base font-semibold text-zinc-200 mb-2">
                {name}
              </h3>
              <p className="text-sm text-zinc-500 mb-4 leading-relaxed">
                {info.description}
              </p>
              <div className="pt-3 border-t border-zinc-800">
                <p className="text-xs text-zinc-500">
                  <span className="text-zinc-300 font-medium">
                    {info.theoremCount.toLocaleString()}
                  </span>{' '}
                  theorems discovered
                </p>
              </div>
            </div>
          )
        })}
      </div>
    </div>
  )
}
