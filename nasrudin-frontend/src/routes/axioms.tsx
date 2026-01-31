import { createFileRoute } from "@tanstack/react-router";
import DomainBadge from "../components/DomainBadge";
import { domainDisplay } from "../lib/api";
import { useAxioms } from "../lib/queries";
import type { ApiAxiom } from "../lib/types";

export const Route = createFileRoute("/axioms")({ component: AxiomsPage });

function AxiomsPage() {
	const { data, isLoading, error } = useAxioms();

	if (isLoading) {
		return (
			<div className="p-8 max-w-5xl mx-auto">
				<div className="animate-pulse space-y-4">
					<div className="h-8 bg-slate-200 rounded w-48" />
					<div className="h-4 bg-slate-200 rounded w-64" />
					<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
						{["s1", "s2", "s3", "s4", "s5", "s6"].map((id) => (
							<div key={id} className="h-24 bg-slate-100 rounded-lg" />
						))}
					</div>
				</div>
			</div>
		);
	}

	if (error) {
		return (
			<div className="p-8 max-w-5xl mx-auto">
				<div className="bg-red-50 border border-red-200 rounded-lg p-4">
					<p className="text-red-700 text-sm">
						Failed to load axioms: {error.message}
					</p>
				</div>
			</div>
		);
	}

	const axioms = data?.axioms ?? [];

	// Group axioms by domain for display
	const grouped: Record<string, ApiAxiom[]> = {};
	for (const axiom of axioms) {
		const display = domainDisplay(axiom.domain);
		if (!grouped[display]) grouped[display] = [];
		grouped[display].push(axiom);
	}
	const domains = Object.entries(grouped).sort(
		([, a], [, b]) => b.length - a.length,
	);

	return (
		<div className="p-8 max-w-5xl mx-auto">
			<div className="mb-8">
				<h1 className="text-2xl font-bold text-slate-900">Axioms</h1>
				<p className="text-sm text-slate-500 mt-1">
					{data?.total ?? 0} seed axioms loaded from PhysLean, grouped by domain
				</p>
			</div>

			<div className="space-y-10">
				{domains.map(([domain, domainAxioms]) => (
					<section key={domain}>
						<div className="flex items-center gap-3 mb-4">
							<h2 className="text-lg font-semibold text-slate-800">{domain}</h2>
							<span className="text-xs text-slate-500">
								{domainAxioms.length} axiom
								{domainAxioms.length !== 1 && "s"}
							</span>
						</div>
						<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
							{domainAxioms.map((axiom) => (
								<div
									key={axiom.name}
									className="bg-white border border-slate-200 rounded-lg p-4 hover:border-amber-300 transition-colors"
								>
									<div className="flex items-center justify-between mb-2">
										<h3 className="text-sm font-medium text-slate-700 truncate">
											{axiom.name}
										</h3>
										<DomainBadge domain={axiom.domain} />
									</div>
									{axiom.description && (
										<p className="text-xs text-slate-500 line-clamp-2">
											{axiom.description}
										</p>
									)}
								</div>
							))}
						</div>
					</section>
				))}
			</div>
		</div>
	);
}
