import { createFileRoute, Link } from "@tanstack/react-router";
import "katex/dist/katex.min.css";
import { BlockMath } from "react-katex";
import DomainBadge from "../components/DomainBadge";
import { RouteError } from "../components/RouteError";
import {
	domainDisplay,
	epochToIso,
	originOperator,
	theoremHexId,
	totalFitness,
} from "../lib/api";
import { recentTheoremsQueryOptions, useRecentTheorems } from "../lib/queries";
import { useDiscoveryStream } from "../lib/sse";

export const Route = createFileRoute("/timeline")({
	loader: ({ context: { queryClient } }) => {
		queryClient.ensureQueryData(recentTheoremsQueryOptions(20));
	},
	head: () => ({
		meta: [{ title: "Timeline — Nasrudin" }],
	}),
	pendingComponent: () => (
		<div className="p-8 max-w-4xl mx-auto">
			<div className="animate-pulse space-y-6">
				<div className="h-8 bg-slate-200 rounded w-1/4" />
				{[1, 2, 3, 4].map((i) => (
					<div key={i} className="pl-12">
						<div className="bg-white border border-slate-200 rounded-lg p-4 h-28" />
					</div>
				))}
			</div>
		</div>
	),
	errorComponent: ({ error, reset }) => (
		<RouteError error={error} reset={reset} />
	),
	component: TimelinePage,
});

function formatTime(iso: string): string {
	const date = new Date(iso);
	return date.toLocaleTimeString("en-US", {
		hour: "2-digit",
		minute: "2-digit",
		second: "2-digit",
		hour12: false,
	});
}

function formatDate(iso: string): string {
	const date = new Date(iso);
	return date.toLocaleDateString("en-US", {
		year: "numeric",
		month: "short",
		day: "numeric",
	});
}

const operatorColors: Record<string, string> = {
	Crossover: "bg-blue-50 text-blue-700 border-blue-200",
	Mutation: "bg-emerald-50 text-emerald-700 border-emerald-200",
	Selection: "bg-amber-50 text-amber-700 border-amber-200",
	Axiom: "bg-violet-50 text-violet-700 border-violet-200",
	Simplification: "bg-slate-50 text-slate-700 border-slate-200",
};

function TimelinePage() {
	const { data, isLoading, error } = useRecentTheorems(20);
	const liveEvents = useDiscoveryStream();

	const recentTheorems = data?.theorems ?? [];

	return (
		<div className="p-8 max-w-4xl mx-auto">
			<div className="mb-8">
				<h1 className="text-2xl font-bold text-slate-900">Timeline</h1>
				<p className="text-sm text-slate-500 mt-1">
					Chronological record of discovered theorems
				</p>
			</div>

			{error && (
				<div className="mb-6 bg-red-50 border border-red-200 rounded-lg px-4 py-3 text-sm text-red-700">
					Failed to load timeline: {error.message}
				</div>
			)}

			<div className="relative">
				<div className="absolute left-4 top-0 bottom-0 w-px bg-slate-200" />

				<div className="space-y-6">
					{/* Live SSE events appear at top */}
					{liveEvents.map((event) => {
						const iso = epochToIso(event.timestamp);

						return (
							<div key={`live-${event.theorem_id}`} className="relative pl-12">
								<div className="absolute left-2.5 top-5 w-3 h-3 rounded-full bg-emerald-500 border-2 border-white animate-pulse" />

								<Link
									to="/theorem/$theoremId"
									params={{ theoremId: event.theorem_id }}
									className="block bg-emerald-50 border border-emerald-200 rounded-lg p-4 hover:border-emerald-300 hover:shadow-sm transition-all"
								>
									<div className="flex items-center justify-between mb-3 flex-wrap gap-2">
										<div className="flex items-center gap-2 text-xs text-slate-500">
											<span className="text-emerald-700 font-medium">LIVE</span>
											<span className="text-slate-300">|</span>
											<span className="font-mono">{formatTime(iso)}</span>
										</div>
										<DomainBadge domain={domainDisplay(event.domain)} />
									</div>
									<div className="overflow-x-auto">
										<BlockMath math={event.latex || event.canonical} />
									</div>
									<div className="mt-2 flex items-center gap-3 text-xs text-slate-500">
										<span>depth {event.depth}</span>
										<span>
											fitness {(totalFitness(event.fitness) * 100).toFixed(1)}%
										</span>
										<span>gen {event.generation}</span>
									</div>
								</Link>
							</div>
						);
					})}

					{/* DB-loaded recent theorems */}
					{isLoading
						? [1, 2, 3, 4].map((i) => (
								<div key={i} className="relative pl-12">
									<div className="absolute left-2.5 top-5 w-3 h-3 rounded-full bg-slate-300 border-2 border-white" />
									<div className="bg-white border border-slate-200 rounded-lg p-4 animate-pulse h-28" />
								</div>
							))
						: recentTheorems.map((thm) => {
								const hexId = theoremHexId(thm.id);
								const operator = originOperator(thm.origin);
								const opColor =
									operatorColors[operator.split(" ")[0]] ??
									"bg-slate-50 text-slate-600 border-slate-200";
								const iso = epochToIso(thm.created_at);

								return (
									<div key={hexId} className="relative pl-12">
										<div className="absolute left-2.5 top-5 w-3 h-3 rounded-full bg-blue-500 border-2 border-white" />

										<Link
											to="/theorem/$theoremId"
											params={{ theoremId: hexId }}
											className="block bg-white border border-slate-200 rounded-lg p-4 hover:border-slate-300 hover:shadow-sm transition-all"
										>
											<div className="flex items-center justify-between mb-3 flex-wrap gap-2">
												<div className="flex items-center gap-2 text-xs text-slate-500">
													<span>{formatDate(iso)}</span>
													<span className="text-slate-300">|</span>
													<span className="font-mono">{formatTime(iso)}</span>
												</div>
												<div className="flex items-center gap-2">
													<span
														className={`inline-flex items-center px-2 py-0.5 rounded-full text-xs font-medium border ${opColor}`}
													>
														{operator}
													</span>
													<DomainBadge domain={domainDisplay(thm.domain)} />
												</div>
											</div>
											<div className="overflow-x-auto">
												<BlockMath math={thm.latex} />
											</div>
											<div className="mt-2 flex items-center gap-3 text-xs text-slate-500">
												<span>depth {thm.depth}</span>
												<span>
													fitness {(totalFitness(thm.fitness) * 100).toFixed(1)}
													%
												</span>
												<span>gen {thm.generation}</span>
											</div>
										</Link>
									</div>
								);
							})}
				</div>
			</div>
		</div>
	);
}
