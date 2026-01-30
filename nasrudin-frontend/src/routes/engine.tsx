import { createFileRoute } from "@tanstack/react-router";
import { Activity, Beaker, Dna, ShieldCheck } from "lucide-react";
import TheoremCard from "../components/TheoremCard";
import { mockStats, mockTheorems } from "../lib/mock-data";

export const Route = createFileRoute("/engine")({ component: EnginePage });

function EnginePage() {
	const stats = [
		{
			label: "Total Theorems",
			value: mockStats.total_theorems.toLocaleString(),
			icon: Beaker,
			color: "text-blue-600",
			bg: "bg-blue-50",
		},
		{
			label: "Rate (/sec)",
			value: `${mockStats.rate}/s`,
			icon: Activity,
			color: "text-emerald-600",
			bg: "bg-emerald-50",
		},
		{
			label: "Generation",
			value: mockStats.generation.toLocaleString(),
			icon: Dna,
			color: "text-amber-600",
			bg: "bg-amber-50",
		},
		{
			label: "Verified",
			value: `${mockStats.verified_pct}%`,
			icon: ShieldCheck,
			color: "text-violet-600",
			bg: "bg-violet-50",
		},
	];

	const recentTheorems = mockTheorems.slice(0, 4);

	return (
		<div className="p-8 max-w-6xl mx-auto">
			<div className="mb-8">
				<h1 className="text-2xl font-bold text-slate-900">Engine</h1>
				<p className="text-sm text-slate-500 mt-1">
					Real-time overview of the genetic algorithm physics discovery engine
				</p>
			</div>

			<div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-4 gap-4 mb-10">
				{stats.map((stat) => {
					const Icon = stat.icon;
					return (
						<div
							key={stat.label}
							className="bg-white border border-slate-200 rounded-lg p-5"
						>
							<div className="flex items-center justify-between mb-3">
								<span className="text-xs font-medium text-slate-500 uppercase tracking-wider">
									{stat.label}
								</span>
								<div className={`${stat.bg} p-1.5 rounded-md`}>
									<Icon size={16} className={stat.color} />
								</div>
							</div>
							<p className={`text-2xl font-bold ${stat.color}`}>{stat.value}</p>
						</div>
					);
				})}
			</div>

			<div className="mb-10">
				<h2 className="text-lg font-semibold text-slate-800 mb-4">
					Recent Discoveries
				</h2>
				<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
					{recentTheorems.map((thm) => (
						<TheoremCard
							key={thm.id}
							id={thm.id}
							latex={thm.latex}
							domain={thm.domain}
							depth={thm.depth}
							fitness={thm.fitness}
							generation={thm.generation}
						/>
					))}
				</div>
			</div>

			<div className="bg-slate-50 border border-slate-200 rounded-xl p-6">
				<h2 className="text-lg font-semibold text-slate-800 mb-3">
					How It Works
				</h2>
				<p className="text-sm text-slate-600 leading-relaxed">
					The Nasrudin engine uses a genetic algorithm to discover and verify
					physics theorems. Starting from seed axioms in each domain, it applies
					crossover, mutation, and selection operators to evolve new
					mathematical relationships. Each candidate theorem is formally
					verified before being added to the corpus. The fitness score reflects
					how well a theorem integrates with known physics.
				</p>
			</div>
		</div>
	);
}
