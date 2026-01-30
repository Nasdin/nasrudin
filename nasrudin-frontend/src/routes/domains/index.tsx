import { createFileRoute, Link } from "@tanstack/react-router";
import { Atom, Flame, Magnet, Orbit, Rocket, Zap } from "lucide-react";
import DomainBadge from "../../components/DomainBadge";
import { domainDescriptions } from "../../lib/mock-data";

export const Route = createFileRoute("/domains/")({ component: DomainsPage });

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
	const domains = Object.entries(domainDescriptions);

	return (
		<div className="p-8 max-w-5xl mx-auto">
			<div className="mb-8">
				<h1 className="text-2xl font-bold text-slate-900">Domains</h1>
				<p className="text-sm text-slate-500 mt-1">
					Physics domains explored by the genetic algorithm engine
				</p>
			</div>

			<div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
				{domains.map(([name, info]) => {
					const Icon = domainIcons[name] ?? Atom;
					const iconColor = domainIconColors[name] ?? "text-slate-500";

					return (
						<Link
							key={name}
							to="/domains/$domain"
							params={{ domain: name }}
							className="block bg-white border border-slate-200 rounded-lg p-5 hover:border-slate-300 hover:shadow-sm transition-all"
						>
							<div className="flex items-start justify-between mb-4">
								<Icon size={28} className={iconColor} />
								<DomainBadge domain={name} />
							</div>
							<h3 className="text-base font-semibold text-slate-800 mb-2">
								{name}
							</h3>
							<p className="text-sm text-slate-500 mb-4 leading-relaxed">
								{info.description}
							</p>
							<div className="pt-3 border-t border-slate-200">
								<p className="text-xs text-slate-500">
									<span className="text-slate-800 font-medium">
										{info.theoremCount.toLocaleString()}
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
