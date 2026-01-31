import { createFileRoute } from "@tanstack/react-router";
import { Activity, Beaker, Dna, ShieldCheck } from "lucide-react";
import { RouteError } from "../components/RouteError";
import TheoremCard from "../components/TheoremCard";
import { domainDisplay, theoremHexId, totalFitness } from "../lib/api";
import {
	gaStatusQueryOptions,
	recentTheoremsQueryOptions,
	statsQueryOptions,
	useGaStatus,
	useRecentTheorems,
	useStats,
} from "../lib/queries";
import { useStatsStream } from "../lib/sse";

export const Route = createFileRoute("/engine")({
	loader: ({ context: { queryClient } }) => {
		queryClient.ensureQueryData(statsQueryOptions());
		queryClient.ensureQueryData(gaStatusQueryOptions());
		queryClient.ensureQueryData(recentTheoremsQueryOptions(4));
	},
	head: () => ({
		meta: [{ title: "Engine Dashboard — Nasrudin" }],
	}),
	pendingComponent: () => (
		<div className="p-8 max-w-6xl mx-auto">
			<div className="animate-pulse space-y-6">
				<div className="h-8 bg-slate-200 rounded w-1/4" />
				<div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-4 gap-4">
					{[1, 2, 3, 4].map((i) => (
						<div
							key={i}
							className="bg-white border border-slate-200 rounded-lg p-5 h-24"
						/>
					))}
				</div>
				<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
					{[1, 2, 3, 4].map((i) => (
						<div
							key={i}
							className="bg-white border border-slate-200 rounded-lg p-4 h-32"
						/>
					))}
				</div>
			</div>
		</div>
	),
	errorComponent: ({ error, reset }) => (
		<RouteError error={error} reset={reset} />
	),
	component: EnginePage,
});

function EnginePage() {
	const {
		data: dbStats,
		isLoading: statsLoading,
		error: statsError,
	} = useStats();
	const { data: gaStatus } = useGaStatus();
	const liveStatus = useStatsStream();
	// Prefer live SSE data over polled query data
	const effectiveGaStatus = liveStatus ?? gaStatus;
	const { data: recentData, isLoading: recentLoading } = useRecentTheorems(4);

	const stats = [
		{
			label: "Total Theorems",
			value: dbStats
				? dbStats.total_theorems.toLocaleString()
				: statsLoading
					? "..."
					: "\u2014",
			icon: Beaker,
			color: "text-blue-600",
			bg: "bg-blue-50",
		},
		{
			label: "Population",
			value: effectiveGaStatus
				? effectiveGaStatus.total_population.toLocaleString()
				: "...",
			icon: Activity,
			color: "text-emerald-600",
			bg: "bg-emerald-50",
		},
		{
			label: "Generation",
			value: dbStats
				? dbStats.max_generation.toLocaleString()
				: statsLoading
					? "..."
					: "\u2014",
			icon: Dna,
			color: "text-amber-600",
			bg: "bg-amber-50",
		},
		{
			label: "Verified",
			value:
				dbStats && dbStats.total_theorems > 0
					? `${((dbStats.total_verified / dbStats.total_theorems) * 100).toFixed(1)}%`
					: statsLoading
						? "..."
						: "\u2014",
			icon: ShieldCheck,
			color: "text-violet-600",
			bg: "bg-violet-50",
		},
	];

	const recentTheorems = recentData?.theorems ?? [];

	return (
		<div className="p-8 max-w-6xl mx-auto">
			<div className="mb-8">
				<h1 className="text-2xl font-bold text-slate-900">Engine</h1>
				<p className="text-sm text-slate-500 mt-1">
					Real-time overview of the genetic algorithm physics discovery engine
				</p>
			</div>

			{statsError && (
				<div className="mb-6 bg-red-50 border border-red-200 rounded-lg px-4 py-3 text-sm text-red-700">
					Engine unavailable: {statsError.message}
				</div>
			)}

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
				{recentLoading ? (
					<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
						{[1, 2, 3, 4].map((i) => (
							<div
								key={i}
								className="bg-white border border-slate-200 rounded-lg p-4 animate-pulse h-32"
							/>
						))}
					</div>
				) : (
					<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
						{recentTheorems.map((thm) => (
							<TheoremCard
								key={theoremHexId(thm.id)}
								id={theoremHexId(thm.id)}
								latex={thm.latex}
								domain={domainDisplay(thm.domain)}
								depth={thm.depth}
								fitness={totalFitness(thm.fitness)}
								generation={thm.generation}
							/>
						))}
					</div>
				)}
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
