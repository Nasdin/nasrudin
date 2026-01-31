import { createFileRoute, Link } from "@tanstack/react-router";
import "katex/dist/katex.min.css";
import { useMemo, useState } from "react";
import { BlockMath } from "react-katex";
import DomainBadge from "../../components/DomainBadge";
import { RouteError } from "../../components/RouteError";
import {
	domainDisplay,
	epochToIso,
	isVerified,
	originOperator,
	theoremHexId,
	totalFitness,
} from "../../lib/api";
import { mockTheorems } from "../../lib/mock-data";
import { theoremQueryOptions, useTheorem } from "../../lib/queries";

export const Route = createFileRoute("/theorem/$theoremId")({
	loader: ({ context: { queryClient }, params }) => {
		queryClient.ensureQueryData(theoremQueryOptions(params.theoremId));
	},
	head: ({ params }) => ({
		meta: [{ title: `Theorem ${params.theoremId} — Nasrudin` }],
	}),
	pendingComponent: () => (
		<div className="p-8 max-w-3xl mx-auto">
			<div className="animate-pulse space-y-4">
				<div className="h-6 bg-slate-200 rounded w-1/3" />
				<div className="h-40 bg-slate-100 rounded-xl" />
				<div className="h-32 bg-slate-100 rounded-xl" />
			</div>
		</div>
	),
	errorComponent: ({ error, reset }) => (
		<RouteError error={error} reset={reset} />
	),
	component: TheoremDetailPage,
});

// Known theorem calculators keyed by canonical/latex signature
const knownCalculators: Record<
	string,
	{
		variables: Array<{
			name: string;
			symbol: string;
			unit: string;
			defaultValue?: number;
		}>;
		computation: {
			target: string;
			targetSymbol: string;
			targetUnit: string;
			compute: (vars: Record<string, number>) => number;
			resultLatex: (result: number) => string;
		};
	}
> = {};

// Pre-populate from the mock data calculators
for (const thm of mockTheorems) {
	if (thm.variables && thm.computation) {
		knownCalculators[thm.latex] = {
			variables: thm.variables,
			computation: thm.computation,
		};
	}
}

function TheoremDetailPage() {
	const { theoremId } = Route.useParams();
	const { data: theorem, isLoading, error } = useTheorem(theoremId);

	if (isLoading) {
		return (
			<div className="p-8 max-w-3xl mx-auto">
				<div className="animate-pulse space-y-4">
					<div className="h-6 bg-slate-200 rounded w-1/3" />
					<div className="h-40 bg-slate-100 rounded-xl" />
					<div className="h-32 bg-slate-100 rounded-xl" />
				</div>
			</div>
		);
	}

	if (error || !theorem) {
		return (
			<div className="p-8 max-w-3xl mx-auto text-center">
				<h1 className="text-2xl font-bold text-slate-900 mb-2">
					Theorem not found
				</h1>
				<p className="text-slate-500 mb-6">
					{error
						? `Error: ${error.message}`
						: `No theorem with ID "${theoremId}" exists.`}
				</p>
				<Link
					to="/"
					className="text-blue-700 hover:underline text-sm font-medium"
				>
					Back to search
				</Link>
			</div>
		);
	}

	const hexId = theoremHexId(theorem.id);
	const display = domainDisplay(theorem.domain);
	const fitness = totalFitness(theorem.fitness);
	const operator = originOperator(theorem.origin);
	const verified = isVerified(theorem.verified);
	const calc = knownCalculators[theorem.latex];

	return (
		<div className="p-8 max-w-3xl mx-auto">
			<Link
				to="/"
				className="inline-flex items-center text-sm text-slate-500 hover:text-slate-700 mb-6"
			>
				&larr; Back to search
			</Link>

			<div className="bg-white border border-slate-200 rounded-xl p-6 mb-6">
				<div className="flex items-center gap-3 mb-4">
					<DomainBadge domain={display} />
					<span className="text-xs text-slate-500">depth {theorem.depth}</span>
					<span className="text-xs text-slate-500">
						gen {theorem.generation}
					</span>
					{verified ? (
						<span className="inline-flex items-center px-2 py-0.5 rounded-full text-xs font-medium bg-emerald-50 text-emerald-700 border border-emerald-200">
							Verified
						</span>
					) : theorem.verified === "Pending" ? (
						<span className="inline-flex items-center px-2 py-0.5 rounded-full text-xs font-medium bg-amber-50 text-amber-700 border border-amber-200">
							Pending
						</span>
					) : (
						<span className="inline-flex items-center px-2 py-0.5 rounded-full text-xs font-medium bg-red-50 text-red-700 border border-red-200">
							Rejected
						</span>
					)}
				</div>
				{theorem.canonical && (
					<p className="text-sm text-slate-500 font-mono mb-2">
						{theorem.canonical}
					</p>
				)}
				<div className="overflow-x-auto text-lg">
					<BlockMath math={theorem.latex} />
				</div>
			</div>

			{calc && (
				<Calculator variables={calc.variables} computation={calc.computation} />
			)}

			<div className="bg-slate-50 border border-slate-200 rounded-xl p-6 mb-6">
				<h2 className="text-sm font-semibold text-slate-900 mb-3">Metadata</h2>
				<dl className="grid grid-cols-2 gap-x-6 gap-y-2 text-sm">
					<dt className="text-slate-500">Fitness</dt>
					<dd className="text-slate-900 font-medium">
						{(fitness * 100).toFixed(1)}%
					</dd>
					<dt className="text-slate-500">Generation</dt>
					<dd className="text-slate-900 font-medium">
						{theorem.generation.toLocaleString()}
					</dd>
					<dt className="text-slate-500">Depth</dt>
					<dd className="text-slate-900 font-medium">{theorem.depth}</dd>
					<dt className="text-slate-500">Complexity</dt>
					<dd className="text-slate-900 font-medium">{theorem.complexity}</dd>
					<dt className="text-slate-500">Operator</dt>
					<dd className="text-slate-900 font-medium">{operator}</dd>
					<dt className="text-slate-500">Discovered</dt>
					<dd className="text-slate-900 font-medium">
						{new Date(epochToIso(theorem.created_at)).toLocaleString()}
					</dd>
				</dl>
			</div>

			{/* Fitness breakdown */}
			<div className="bg-white border border-slate-200 rounded-xl p-6 mb-6">
				<h2 className="text-sm font-semibold text-slate-900 mb-3">
					Fitness Breakdown
				</h2>
				<div className="grid grid-cols-2 sm:grid-cols-4 gap-3">
					{(
						[
							["Novelty", theorem.fitness.novelty],
							["Complexity", theorem.fitness.complexity],
							["Depth", theorem.fitness.depth],
							["Dimensional", theorem.fitness.dimensional],
							["Symmetry", theorem.fitness.symmetry],
							["Connectivity", theorem.fitness.connectivity],
							["Relevance", theorem.fitness.nasrudin_relevance],
						] as const
					).map(([label, val]) => (
						<div key={label} className="text-center">
							<p className="text-lg font-bold text-slate-900">
								{(val * 100).toFixed(0)}%
							</p>
							<p className="text-xs text-slate-500">{label}</p>
						</div>
					))}
				</div>
			</div>

			{/* Parents / Children */}
			{(theorem.parents.length > 0 || theorem.children.length > 0) && (
				<div className="bg-slate-50 border border-slate-200 rounded-xl p-6 mb-6">
					<h2 className="text-sm font-semibold text-slate-900 mb-3">Lineage</h2>
					{theorem.parents.length > 0 && (
						<div className="mb-3">
							<p className="text-xs text-slate-500 mb-1">Parents</p>
							<div className="flex flex-wrap gap-2">
								{theorem.parents.map((pid) => {
									const phex = theoremHexId(pid);
									return (
										<Link
											key={phex}
											to="/theorem/$theoremId"
											params={{ theoremId: phex }}
											className="text-xs font-mono text-blue-700 hover:underline bg-blue-50 px-2 py-1 rounded"
										>
											{phex}
										</Link>
									);
								})}
							</div>
						</div>
					)}
					{theorem.children.length > 0 && (
						<div>
							<p className="text-xs text-slate-500 mb-1">Children</p>
							<div className="flex flex-wrap gap-2">
								{theorem.children.map((cid) => {
									const chex = theoremHexId(cid);
									return (
										<Link
											key={chex}
											to="/theorem/$theoremId"
											params={{ theoremId: chex }}
											className="text-xs font-mono text-blue-700 hover:underline bg-blue-50 px-2 py-1 rounded"
										>
											{chex}
										</Link>
									);
								})}
							</div>
						</div>
					)}
				</div>
			)}

			<Link
				to="/explore/$theoremId"
				params={{ theoremId: hexId }}
				className="inline-flex items-center text-sm font-medium text-blue-700 hover:underline"
			>
				View derivation graph &rarr;
			</Link>
		</div>
	);
}

function Calculator({
	variables,
	computation,
}: {
	variables: Array<{
		name: string;
		symbol: string;
		unit: string;
		defaultValue?: number;
	}>;
	computation: {
		target: string;
		targetSymbol: string;
		targetUnit: string;
		compute: (vars: Record<string, number>) => number;
		resultLatex: (result: number) => string;
	};
}) {
	const [values, setValues] = useState<Record<string, number>>(() => {
		const initial: Record<string, number> = {};
		for (const v of variables) {
			initial[v.symbol] = v.defaultValue ?? 0;
		}
		return initial;
	});

	const result = useMemo(() => {
		try {
			return computation.compute(values);
		} catch {
			return null;
		}
	}, [values, computation]);

	return (
		<div className="bg-white border border-slate-200 rounded-xl p-6 mb-6">
			<h2 className="text-sm font-semibold text-slate-900 mb-4">Calculator</h2>

			<div className="space-y-3 mb-5">
				{variables.map((v) => (
					<label key={v.symbol} className="flex items-center gap-3">
						<span className="w-28 text-sm text-slate-600 shrink-0">
							<span className="font-medium">{v.symbol}</span>
							<span className="text-slate-400 ml-1">({v.unit})</span>
						</span>
						<input
							type="number"
							value={values[v.symbol]}
							onChange={(e) =>
								setValues((prev) => ({
									...prev,
									[v.symbol]: Number(e.target.value),
								}))
							}
							className="flex-1 border border-slate-200 rounded-lg px-3 py-2 text-sm text-slate-900 focus:outline-none focus:border-blue-500 focus:ring-1 focus:ring-blue-500"
						/>
					</label>
				))}
			</div>

			{result !== null && (
				<div className="bg-slate-50 border border-slate-200 rounded-lg p-4">
					<p className="text-xs text-slate-500 uppercase tracking-wider mb-2">
						Result — {computation.target} ({computation.targetUnit})
					</p>
					<div className="overflow-x-auto">
						<BlockMath math={computation.resultLatex(result)} />
					</div>
				</div>
			)}
		</div>
	);
}
