import { createFileRoute, Link } from "@tanstack/react-router";
import { useVirtualizer } from "@tanstack/react-virtual";
import { useRef } from "react";
import DomainBadge from "../../components/DomainBadge";
import { RouteError } from "../../components/RouteError";
import TheoremCard from "../../components/TheoremCard";
import { domainDisplay, theoremHexId, totalFitness } from "../../lib/api";
import { domainDescriptions } from "../../lib/mock-data";
import {
	domainsQueryOptions,
	searchTheoremsQueryOptions,
	useDomains,
	useSearchTheorems,
} from "../../lib/queries";

export const Route = createFileRoute("/domains/$domain")({
	loader: ({ context: { queryClient }, params }) => {
		const apiDomain = decodeURIComponent(params.domain).replace(/\s+/g, "");
		const searchDomain = apiDomain
			.toLowerCase()
			.replace(/([a-z])([A-Z])/g, "$1_$2")
			.toLowerCase();
		queryClient.ensureQueryData(domainsQueryOptions());
		queryClient.ensureQueryData(
			searchTheoremsQueryOptions({ domain: searchDomain, limit: 50 }),
		);
	},
	head: ({ params }) => ({
		meta: [
			{
				title: `${decodeURIComponent(params.domain)} — Nasrudin`,
			},
		],
	}),
	pendingComponent: () => (
		<div className="p-8 max-w-5xl mx-auto">
			<div className="animate-pulse space-y-6">
				<div className="h-4 bg-slate-200 rounded w-20" />
				<div className="h-8 bg-slate-200 rounded w-1/3" />
				<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
					{[1, 2, 3, 4].map((i) => (
						<div
							key={i}
							className="bg-white border border-slate-200 rounded-lg p-4 h-32"
						/>
					))}
				</div>
			</div>
		</div>
	),
	errorComponent: ({ error, reset }) => (
		<RouteError error={error} reset={reset} />
	),
	component: DomainDetailPage,
});

function DomainDetailPage() {
	const { domain } = Route.useParams();
	const decodedDomain = decodeURIComponent(domain);
	const info = domainDescriptions[decodedDomain];

	// Convert display name to API enum key (e.g., "Special Relativity" -> "SpecialRelativity")
	const apiDomain = decodedDomain.replace(/\s+/g, "");

	const { data: apiCounts } = useDomains();
	const { data, isLoading, error } = useSearchTheorems({
		domain: apiDomain
			.toLowerCase()
			.replace(/([a-z])([A-Z])/g, "$1_$2")
			.toLowerCase(),
		limit: 50,
	});

	const count =
		apiCounts?.[apiDomain] ??
		apiCounts?.[decodedDomain] ??
		info?.theoremCount ??
		0;
	const theorems = data?.theorems ?? [];

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
					{count.toLocaleString()} theorems discovered
				</p>
			</div>

			{error && (
				<div className="mb-6 bg-red-50 border border-red-200 rounded-lg px-4 py-3 text-sm text-red-700">
					Failed to load theorems: {error.message}
				</div>
			)}

			{isLoading ? (
				<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
					{[1, 2, 3, 4].map((i) => (
						<div
							key={i}
							className="bg-white border border-slate-200 rounded-lg p-4 animate-pulse h-32"
						/>
					))}
				</div>
			) : theorems.length > 20 ? (
				<VirtualDomainList theorems={theorems} />
			) : theorems.length > 0 ? (
				<div className="grid grid-cols-1 md:grid-cols-2 gap-4">
					{theorems.map((thm) => (
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
			) : (
				<p className="text-sm text-slate-500">
					No theorems available for this domain yet.
				</p>
			)}
		</div>
	);
}

function VirtualDomainList({
	theorems,
}: {
	theorems: import("../../lib/types").ApiTheorem[];
}) {
	const parentRef = useRef<HTMLDivElement>(null);
	const virtualizer = useVirtualizer({
		count: theorems.length,
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
					const thm = theorems[row.index];
					return (
						<div
							key={row.key}
							style={{
								position: "absolute",
								top: row.start,
								width: "100%",
							}}
						>
							<div className="pb-4 pr-4">
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
