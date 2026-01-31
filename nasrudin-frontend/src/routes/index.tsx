import { createFileRoute, Link } from "@tanstack/react-router";
import { Search as SearchIcon } from "lucide-react";
import { useState } from "react";
import "katex/dist/katex.min.css";
import { BlockMath } from "react-katex";
import { useDebouncedValue } from "@tanstack/react-pacer/debouncer";
import DomainBadge from "../components/DomainBadge";
import { RouteError } from "../components/RouteError";
import TheoremCard from "../components/TheoremCard";
import {
	domainDisplay,
	originOperator,
	theoremHexId,
	totalFitness,
} from "../lib/api";
import { domainDescriptions } from "../lib/mock-data";
import {
	domainsQueryOptions,
	recentTheoremsQueryOptions,
	statsQueryOptions,
	useDomains,
	useRecentTheorems,
	useSearchTheorems,
	useStats,
} from "../lib/queries";

export const Route = createFileRoute("/")({
	loader: ({ context: { queryClient } }) => {
		queryClient.ensureQueryData(statsQueryOptions());
		queryClient.ensureQueryData(domainsQueryOptions());
		queryClient.ensureQueryData(recentTheoremsQueryOptions(5));
	},
	head: () => ({
		meta: [{ title: "Nasrudin — Search Physics Theorems" }],
	}),
	pendingComponent: () => (
		<div className="max-w-5xl mx-auto px-6 pt-16">
			<div className="animate-pulse space-y-6">
				<div className="h-8 bg-slate-200 rounded w-2/3 mx-auto" />
				<div className="h-4 bg-slate-100 rounded w-1/3 mx-auto" />
				<div className="h-12 bg-slate-100 rounded-xl max-w-2xl mx-auto" />
				<div className="grid grid-cols-2 md:grid-cols-3 gap-3 mt-8">
					{[1, 2, 3, 4, 5, 6].map((i) => (
						<div key={i} className="h-20 bg-slate-100 rounded-lg" />
					))}
				</div>
			</div>
		</div>
	),
	errorComponent: ({ error, reset }) => (
		<RouteError error={error} reset={reset} />
	),
	component: LandingPage,
});

function LandingPage() {
	const [query, setQuery] = useState("");
	const [debouncedQuery] = useDebouncedValue(query, { wait: 300 });

	const { data: stats } = useStats();
	const { data: domainsData } = useDomains();
	const { data: recentData } = useRecentTheorems(5);
	const { data: searchData, isLoading: searchLoading } = useSearchTheorems(
		debouncedQuery.trim()
			? { latex: debouncedQuery.trim(), limit: 10 }
			: { limit: 0 },
	);

	const filteredResults =
		debouncedQuery.trim() ? (searchData?.theorems ?? []) : [];

	// Merge API domain counts with client-side descriptions
	const domains = Object.entries(domainDescriptions).map(([name, info]) => {
		const apiKey = name.replace(/\s+/g, "");
		const count =
			domainsData?.[apiKey] ?? domainsData?.[name] ?? info.theoremCount;
		return { name, description: info.description, theoremCount: count };
	});

	const recentEntries = recentData?.theorems ?? [];
	const featuredTheorems = recentData?.theorems?.slice(0, 4) ?? [];

	return (
		<div className="max-w-5xl mx-auto px-6">
			{/* Hero + Search */}
			<section className="pt-16 pb-10 text-center">
				<h1 className="text-3xl font-bold text-slate-900 mb-2">
					Search formally verified physics theorems
				</h1>
				<p className="text-slate-500 mb-8">
					{stats
						? stats.total_theorems.toLocaleString()
						: "..."}{" "}
					theorems discovered by genetic algorithm
				</p>

				<div className="relative max-w-2xl mx-auto">
					<SearchIcon
						size={20}
						className="absolute left-4 top-1/2 -translate-y-1/2 text-slate-400"
					/>
					<input
						type="text"
						value={query}
						onChange={(e) => setQuery(e.target.value)}
						placeholder="Search by formula, domain, or name..."
						className="w-full border border-slate-300 rounded-xl pl-12 pr-4 py-3 text-slate-900 placeholder-slate-400 bg-white focus:outline-none focus:border-blue-500 focus:ring-1 focus:ring-blue-500 shadow-sm transition-colors"
					/>
				</div>

				{query.trim() && (
					<div className="max-w-2xl mx-auto mt-4 bg-slate-50 border border-slate-200 rounded-lg p-3 text-left">
						<p className="text-xs text-slate-500 uppercase tracking-wider mb-1">
							Preview
						</p>
						<div className="overflow-x-auto">
							<BlockMath math={query} errorColor="#ef4444" />
						</div>
					</div>
				)}
			</section>

			{/* Search Results */}
			{query.trim() && (
				<section className="pb-10">
					<p className="text-sm text-slate-500 mb-4">
						{searchLoading
							? "Searching..."
							: `${filteredResults.length} result${filteredResults.length !== 1 ? "s" : ""} for \u201c${debouncedQuery}\u201d`}
					</p>
					<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
						{filteredResults.map((thm) => (
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
				</section>
			)}

			{/* Content below — only when not searching */}
			{!query.trim() && (
				<>
					{/* Live Discoveries */}
					<section className="pb-10">
						<h2 className="text-lg font-semibold text-slate-900 mb-4">
							Live Discoveries
						</h2>
						<div className="space-y-2">
							{recentEntries.map((entry) => {
								const hexId = theoremHexId(entry.id);
								return (
									<Link
										key={hexId}
										to="/theorem/$theoremId"
										params={{ theoremId: hexId }}
										className="flex items-center justify-between bg-slate-50 border border-slate-200 rounded-lg px-4 py-3 hover:border-slate-300 hover:shadow-sm transition-all"
									>
										<div className="flex items-center gap-3 overflow-hidden">
											<DomainBadge domain={domainDisplay(entry.domain)} />
											<span className="text-sm text-slate-700 font-mono truncate">
												{entry.latex}
											</span>
										</div>
										<span className="text-xs text-slate-400 shrink-0 ml-4">
											{originOperator(entry.origin)}
										</span>
									</Link>
								);
							})}
						</div>
					</section>

					{/* Browse by Domain */}
					<section className="pb-10">
						<h2 className="text-lg font-semibold text-slate-900 mb-4">
							Browse by Domain
						</h2>
						<div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-6 gap-3">
							{domains.map((d) => (
								<Link
									key={d.name}
									to="/domains/$domain"
									params={{ domain: d.name }}
									className="bg-white border border-slate-200 rounded-lg p-4 hover:border-slate-300 hover:shadow-sm transition-all text-center"
								>
									<p className="text-sm font-medium text-slate-900 mb-1">
										{d.name}
									</p>
									<p className="text-xs text-slate-500">
										{d.theoremCount.toLocaleString()} theorems
									</p>
								</Link>
							))}
						</div>
					</section>

					{/* Featured Theorems */}
					<section className="pb-16">
						<h2 className="text-lg font-semibold text-slate-900 mb-4">
							Featured Theorems
						</h2>
						<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
							{featuredTheorems.map((thm) => (
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
					</section>
				</>
			)}
		</div>
	);
}
