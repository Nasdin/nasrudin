import { createFileRoute } from "@tanstack/react-router";
import "katex/dist/katex.min.css";
import { BlockMath } from "react-katex";
import DomainBadge from "../components/DomainBadge";
import { mockAxioms } from "../lib/mock-data";

export const Route = createFileRoute("/axioms")({ component: AxiomsPage });

function AxiomsPage() {
	const domains = Object.entries(mockAxioms);

	return (
		<div className="p-8 max-w-5xl mx-auto">
			<div className="mb-8">
				<h1 className="text-2xl font-bold text-slate-900">Axioms</h1>
				<p className="text-sm text-slate-500 mt-1">
					Seed axioms that drive the genetic algorithm, grouped by domain
				</p>
			</div>

			<div className="space-y-10">
				{domains.map(([domain, axioms]) => (
					<section key={domain}>
						<div className="flex items-center gap-3 mb-4">
							<h2 className="text-lg font-semibold text-slate-800">{domain}</h2>
							<span className="text-xs text-slate-500">
								{axioms.length} axiom{axioms.length !== 1 && "s"}
							</span>
						</div>
						<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
							{axioms.map((axiom) => (
								<div
									key={axiom.id}
									className="bg-white border border-slate-200 rounded-lg p-4 hover:border-amber-300 transition-colors"
								>
									<div className="flex items-center justify-between mb-3">
										<h3 className="text-sm font-medium text-slate-700">
											{axiom.name}
										</h3>
										<DomainBadge domain={axiom.domain} />
									</div>
									<div className="overflow-x-auto">
										<BlockMath math={axiom.latex} />
									</div>
								</div>
							))}
						</div>
					</section>
				))}
			</div>
		</div>
	);
}
