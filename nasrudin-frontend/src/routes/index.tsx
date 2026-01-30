import { createFileRoute, Link } from "@tanstack/react-router";
import { Search as SearchIcon } from "lucide-react";
import { useState } from "react";
import "katex/dist/katex.min.css";
import { BlockMath } from "react-katex";
import DomainBadge from "../components/DomainBadge";
import TheoremCard from "../components/TheoremCard";
import {
	domainDescriptions,
	mockStats,
	mockTheorems,
	mockTimelineEntries,
} from "../lib/mock-data";

export const Route = createFileRoute("/")({ component: LandingPage });

function LandingPage() {
	const [query, setQuery] = useState("");

	const filteredResults = query.trim()
		? mockTheorems.filter(
				(t) =>
					t.latex.toLowerCase().includes(query.toLowerCase()) ||
					t.domain.toLowerCase().includes(query.toLowerCase()) ||
					t.name?.toLowerCase().includes(query.toLowerCase()),
			)
		: [];

	const featuredIds = ["thm-001", "thm-002", "thm-003", "thm-004"];
	const featuredTheorems = mockTheorems.filter((t) =>
		featuredIds.includes(t.id),
	);

	const domains = Object.entries(domainDescriptions);
	const recentEntries = mockTimelineEntries.slice(0, 5);

	return (
		<div className="max-w-5xl mx-auto px-6">
			{/* Hero + Search */}
			<section className="pt-16 pb-10 text-center">
				<h1 className="text-3xl font-bold text-slate-900 mb-2">
					Search formally verified physics theorems
				</h1>
				<p className="text-slate-500 mb-8">
					{mockStats.total_theorems.toLocaleString()} theorems discovered by
					genetic algorithm
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
						{filteredResults.length} result{filteredResults.length !== 1 && "s"}{" "}
						for &ldquo;{query}&rdquo;
					</p>
					<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
						{filteredResults.map((thm) => (
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
							{recentEntries.map((entry) => (
								<Link
									key={entry.id}
									to="/theorem/$theoremId"
									params={{ theoremId: entry.theorem.id }}
									className="flex items-center justify-between bg-slate-50 border border-slate-200 rounded-lg px-4 py-3 hover:border-slate-300 hover:shadow-sm transition-all"
								>
									<div className="flex items-center gap-3 overflow-hidden">
										<DomainBadge domain={entry.theorem.domain} />
										<span className="text-sm text-slate-700 font-mono truncate">
											{entry.theorem.latex}
										</span>
									</div>
									<span className="text-xs text-slate-400 shrink-0 ml-4">
										{entry.operator}
									</span>
								</Link>
							))}
						</div>
					</section>

					{/* Browse by Domain */}
					<section className="pb-10">
						<h2 className="text-lg font-semibold text-slate-900 mb-4">
							Browse by Domain
						</h2>
						<div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-6 gap-3">
							{domains.map(([name, info]) => (
								<Link
									key={name}
									to="/domains/$domain"
									params={{ domain: name }}
									className="bg-white border border-slate-200 rounded-lg p-4 hover:border-slate-300 hover:shadow-sm transition-all text-center"
								>
									<p className="text-sm font-medium text-slate-900 mb-1">
										{name}
									</p>
									<p className="text-xs text-slate-500">
										{info.theoremCount.toLocaleString()} theorems
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
					</section>
				</>
			)}
		</div>
	);
}
