import { createFileRoute, Link } from "@tanstack/react-router";
import "katex/dist/katex.min.css";
import { useMemo, useState } from "react";
import { BlockMath } from "react-katex";
import DomainBadge from "../../components/DomainBadge";
import { mockTheorems } from "../../lib/mock-data";

export const Route = createFileRoute("/theorem/$theoremId")({
	component: TheoremDetailPage,
});

function TheoremDetailPage() {
	const { theoremId } = Route.useParams();
	const theorem = mockTheorems.find((t) => t.id === theoremId);

	if (!theorem) {
		return (
			<div className="p-8 max-w-3xl mx-auto text-center">
				<h1 className="text-2xl font-bold text-slate-900 mb-2">
					Theorem not found
				</h1>
				<p className="text-slate-500 mb-6">
					No theorem with ID "{theoremId}" exists.
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
					<DomainBadge domain={theorem.domain} />
					<span className="text-xs text-slate-500">depth {theorem.depth}</span>
					<span className="text-xs text-slate-500">
						gen {theorem.generation}
					</span>
				</div>
				{theorem.name && (
					<h1 className="text-xl font-bold text-slate-900 mb-4">
						{theorem.name}
					</h1>
				)}
				<div className="overflow-x-auto text-lg">
					<BlockMath math={theorem.latex} />
				</div>
			</div>

			{theorem.variables && theorem.computation && (
				<Calculator
					variables={theorem.variables}
					computation={theorem.computation}
				/>
			)}

			<div className="bg-slate-50 border border-slate-200 rounded-xl p-6 mb-6">
				<h2 className="text-sm font-semibold text-slate-900 mb-3">Metadata</h2>
				<dl className="grid grid-cols-2 gap-x-6 gap-y-2 text-sm">
					<dt className="text-slate-500">Fitness</dt>
					<dd className="text-slate-900 font-medium">
						{(theorem.fitness * 100).toFixed(1)}%
					</dd>
					<dt className="text-slate-500">Generation</dt>
					<dd className="text-slate-900 font-medium">
						{theorem.generation.toLocaleString()}
					</dd>
					<dt className="text-slate-500">Depth</dt>
					<dd className="text-slate-900 font-medium">{theorem.depth}</dd>
					{theorem.operator && (
						<>
							<dt className="text-slate-500">Operator</dt>
							<dd className="text-slate-900 font-medium">{theorem.operator}</dd>
						</>
					)}
					{theorem.timestamp && (
						<>
							<dt className="text-slate-500">Discovered</dt>
							<dd className="text-slate-900 font-medium">
								{new Date(theorem.timestamp).toLocaleString()}
							</dd>
						</>
					)}
				</dl>
			</div>

			<Link
				to="/explore/$theoremId"
				params={{ theoremId: "demo" }}
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
	variables: NonNullable<(typeof mockTheorems)[0]["variables"]>;
	computation: NonNullable<(typeof mockTheorems)[0]["computation"]>;
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
