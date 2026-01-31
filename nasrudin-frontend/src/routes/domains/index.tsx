import { createFileRoute, Link } from "@tanstack/react-router";
import { Atom, Flame, Magnet, Orbit, Rocket, Zap } from "lucide-react";
import DomainBadge from "../../components/DomainBadge";
import { RouteError } from "../../components/RouteError";
import { domainDescriptions } from "../../lib/mock-data";
import { domainsQueryOptions, useDomains } from "../../lib/queries";

export const Route = createFileRoute("/domains/")({
	loader: ({ context: { queryClient } }) => {
		queryClient.ensureQueryData(domainsQueryOptions());
	},
	head: () => ({
		meta: [{ title: "Domains — Nasrudin" }],
	}),
	pendingComponent: () => (
		<div className="p-8 max-w-5xl mx-auto">
			<div className="animate-pulse space-y-6">
				<div className="h-8 bg-slate-200 rounded w-1/4" />
				<div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
					{[1, 2, 3, 4, 5, 6].map((i) => (
						<div
							key={i}
							className="bg-white border border-slate-200 rounded-lg p-5 h-40"
						/>
					))}
				</div>
			</div>
		</div>
	),
	errorComponent: ({ error, reset }) => (
		<RouteError error={error} reset={reset} />
	),
	component: DomainsPage,
});

const domainIcons: Record<string, React.ElementType> = {
	"Classical Mechanics": Rocket,
	Electromagnetism: Zap,
	"Special Relativity": Orbit,
	"General Relativity": Magnet,
	"Quantum Mechanics": Atom,
	Thermodynamics: Flame,
};

const domainIconColors: Record<string, string> = {
	"Classical Mechanics": "text-blue-600",
	Electromagnetism: "text-amber-600",
	"Special Relativity": "text-red-600",
	"General Relativity": "text-rose-600",
	"Quantum Mechanics": "text-violet-600",
	Thermodynamics: "text-emerald-600",
};

function DomainsPage() {
	const { data: apiCounts } = useDomains();

	// Merge API counts with client-side descriptions
	const domains = Object.entries(domainDescriptions).map(([name, info]) => {
		const apiKey = name.replace(/\s+/g, "");
		const count = apiCounts?.[apiKey] ?? apiCounts?.[name] ?? info.theoremCount;
		return { name, description: info.description, theoremCount: count };
	});

	return (
		<div className="p-8 max-w-5xl mx-auto">
			<div className="mb-8">
				<h1 className="text-2xl font-bold text-slate-900">Domains</h1>
				<p className="text-sm text-slate-500 mt-1">
					Physics domains explored by the genetic algorithm engine
				</p>
			</div>

			<div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
				{domains.map((d) => {
					const Icon = domainIcons[d.name] ?? Atom;
					const iconColor = domainIconColors[d.name] ?? "text-slate-500";

					return (
						<Link
							key={d.name}
							to="/domains/$domain"
							params={{ domain: d.name }}
							className="block bg-white border border-slate-200 rounded-lg p-5 hover:border-slate-300 hover:shadow-sm transition-all"
						>
							<div className="flex items-start justify-between mb-4">
								<Icon size={28} className={iconColor} />
								<DomainBadge domain={d.name} />
							</div>
							<h3 className="text-base font-semibold text-slate-800 mb-2">
								{d.name}
							</h3>
							<p className="text-sm text-slate-500 mb-4 leading-relaxed">
								{d.description}
							</p>
							<div className="pt-3 border-t border-slate-200">
								<p className="text-xs text-slate-500">
									<span className="text-slate-800 font-medium">
										{d.theoremCount.toLocaleString()}
									</span>{" "}
									theorems discovered
								</p>
							</div>
						</Link>
					);
				})}
			</div>
		</div>
	);
}
