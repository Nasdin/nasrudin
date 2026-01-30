import { createFileRoute } from "@tanstack/react-router";
import { Search as SearchIcon } from "lucide-react";
import { useState } from "react";
import "katex/dist/katex.min.css";
import { BlockMath } from "react-katex";
import TheoremCard from "../components/TheoremCard";
import { mockTheorems } from "../lib/mock-data";

export const Route = createFileRoute("/search")({ component: SearchPage });

function SearchPage() {
	const [query, setQuery] = useState("");

	const filteredResults = query.trim()
		? mockTheorems.filter(
				(t) =>
					t.latex.toLowerCase().includes(query.toLowerCase()) ||
					t.domain.toLowerCase().includes(query.toLowerCase()) ||
					t.name?.toLowerCase().includes(query.toLowerCase()),
			)
		: mockTheorems;

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

			<div>
				<p className="text-sm text-slate-500 mb-4">
					{filteredResults.length} result{filteredResults.length !== 1 && "s"}
					{query.trim() ? ` for "${query}"` : ""}
				</p>
				<div className="space-y-4">
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
			</div>
		</div>
	);
}
