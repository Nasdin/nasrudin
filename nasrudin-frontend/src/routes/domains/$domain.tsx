import { createFileRoute, Link } from "@tanstack/react-router";
import DomainBadge from "../../components/DomainBadge";
import TheoremCard from "../../components/TheoremCard";
import { domainDescriptions, mockTheorems } from "../../lib/mock-data";

export const Route = createFileRoute("/domains/$domain")({
	component: DomainDetailPage,
});

function DomainDetailPage() {
	const { domain } = Route.useParams();
	const decodedDomain = decodeURIComponent(domain);
	const info = domainDescriptions[decodedDomain];
	const theorems = mockTheorems.filter((t) => t.domain === decodedDomain);

	if (!info) {
		return (
			<div className="p-8 max-w-3xl mx-auto text-center">
				<h1 className="text-2xl font-bold text-slate-900 mb-2">
					Domain not found
				</h1>
				<p className="text-slate-500 mb-6">
					No domain named &ldquo;{decodedDomain}&rdquo; exists.
				</p>
				<Link
					to="/domains"
					className="text-blue-700 hover:underline text-sm font-medium"
				>
					Back to domains
				</Link>
			</div>
		);
	}

	return (
		<div className="p-8 max-w-5xl mx-auto">
			<Link
				to="/domains"
				className="inline-flex items-center text-sm text-slate-500 hover:text-slate-700 mb-6"
			>
				&larr; All domains
			</Link>

			<div className="mb-8">
				<div className="flex items-center gap-3 mb-2">
					<h1 className="text-2xl font-bold text-slate-900">{decodedDomain}</h1>
					<DomainBadge domain={decodedDomain} />
				</div>
				<p className="text-sm text-slate-500">{info.description}</p>
				<p className="text-xs text-slate-400 mt-1">
					{info.theoremCount.toLocaleString()} theorems discovered
				</p>
			</div>

			{theorems.length > 0 ? (
				<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
					{theorems.map((thm) => (
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
			) : (
				<p className="text-sm text-slate-500">
					No mock theorems available for this domain.
				</p>
			)}
		</div>
	);
}
