import { createFileRoute } from "@tanstack/react-router";
import { Search as SearchIcon } from "lucide-react";
import { useRef, useState } from "react";
import "katex/dist/katex.min.css";
import { useDebouncedValue } from "@tanstack/react-pacer/debouncer";
import { useVirtualizer } from "@tanstack/react-virtual";
import { BlockMath } from "react-katex";
import { RouteError } from "../components/RouteError";
import TheoremCard from "../components/TheoremCard";
import { domainDisplay, theoremHexId, totalFitness } from "../lib/api";
import { useSearchTheorems } from "../lib/queries";

export const Route = createFileRoute("/search")({
	head: () => ({
		meta: [{ title: "Search — Nasrudin" }],
	}),
	pendingComponent: () => (
		<div className="p-8 max-w-4xl mx-auto">
			<div className="animate-pulse space-y-4">
				<div className="h-8 bg-slate-200 rounded w-1/4" />
				<div className="h-12 bg-slate-100 rounded-lg" />
				<div className="space-y-4 mt-6">
					{[1, 2, 3].map((i) => (
						<div
							key={i}
							className="bg-white border border-slate-200 rounded-lg p-4 h-28"
						/>
					))}
				</div>
			</div>
		</div>
	),
	errorComponent: ({ error, reset }) => (
		<RouteError error={error} reset={reset} />
	),
	component: SearchPage,
});

function SearchPage() {
	const [query, setQuery] = useState("");
	const [debouncedQuery] = useDebouncedValue(query, { wait: 300 });

	const { data, isLoading, error } = useSearchTheorems(
		debouncedQuery.trim()
			? { latex: debouncedQuery.trim(), limit: 50 }
			: { limit: 50 },
	);

	const results = data?.theorems ?? [];

	return (
		<div className="p-8 max-w-4xl mx-auto">
			<div className="mb-8">
				<h1 className="text-2xl font-bold text-slate-900">Search</h1>
				<p className="text-sm text-slate-500 mt-1">
					Search theorems by LaTeX formula or domain
				</p>
			</div>

			<div className="relative mb-6">
				<SearchIcon
					size={20}
					className="absolute left-4 top-1/2 -translate-y-1/2 text-slate-400"
				/>
				<input
					type="text"
					value={query}
					onChange={(e) => setQuery(e.target.value)}
					placeholder="Type LaTeX formula..."
					className="w-full bg-white border border-slate-300 rounded-lg pl-12 pr-4 py-3 text-slate-900 placeholder-slate-400 focus:outline-none focus:border-blue-500 focus:ring-1 focus:ring-blue-500 transition-colors"
				/>
			</div>

			{query.trim() && (
				<div className="mb-8 bg-slate-50 border border-slate-200 rounded-lg p-4">
					<p className="text-xs text-slate-500 uppercase tracking-wider mb-2">
						Preview
					</p>
					<div className="overflow-x-auto">
						<BlockMath math={query} errorColor="#ef4444" />
					</div>
				</div>
			)}

			{error && (
				<div className="mb-6 bg-red-50 border border-red-200 rounded-lg px-4 py-3 text-sm text-red-700">
					Search failed: {error.message}
				</div>
			)}

			<div>
				<p className="text-sm text-slate-500 mb-4">
					{isLoading
						? "Searching..."
						: `${data?.total ?? 0} result${(data?.total ?? 0) !== 1 ? "s" : ""}${debouncedQuery.trim() ? ` for "${debouncedQuery}"` : ""}`}
				</p>
				{isLoading ? (
					<div className="space-y-4">
						{[1, 2, 3].map((i) => (
							<div
								key={i}
								className="bg-white border border-slate-200 rounded-lg p-4 animate-pulse h-28"
							/>
						))}
					</div>
				) : results.length > 20 ? (
					<VirtualTheoremList results={results} />
				) : (
					<div className="space-y-4">
						{results.map((thm) => (
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
		</div>
	);
}

function VirtualTheoremList({
	results,
}: {
	results: import("../lib/types").ApiTheorem[];
}) {
	const parentRef = useRef<HTMLDivElement>(null);
	const virtualizer = useVirtualizer({
		count: results.length,
		getScrollElement: () => parentRef.current,
		estimateSize: () => 160,
		overscan: 5,
	});

	return (
		<div ref={parentRef} className="h-[600px] overflow-auto">
			<div
				style={{
					height: virtualizer.getTotalSize(),
					position: "relative",
				}}
			>
				{virtualizer.getVirtualItems().map((row) => {
					const thm = results[row.index];
					return (
						<div
							key={row.key}
							style={{
								position: "absolute",
								top: row.start,
								width: "100%",
							}}
						>
							<div className="pb-4">
								<TheoremCard
									id={theoremHexId(thm.id)}
									latex={thm.latex}
									domain={domainDisplay(thm.domain)}
									depth={thm.depth}
									fitness={totalFitness(thm.fitness)}
									generation={thm.generation}
								/>
							</div>
						</div>
					);
				})}
			</div>
		</div>
	);
}
