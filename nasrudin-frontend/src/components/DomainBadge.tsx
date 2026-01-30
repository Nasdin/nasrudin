const domainColors: Record<string, string> = {
	"Classical Mechanics": "bg-blue-50 text-blue-700 border-blue-200",
	Electromagnetism: "bg-amber-50 text-amber-700 border-amber-200",
	"Special Relativity": "bg-red-50 text-red-700 border-red-200",
	"General Relativity": "bg-rose-50 text-rose-700 border-rose-200",
	"Quantum Mechanics": "bg-violet-50 text-violet-700 border-violet-200",
	Thermodynamics: "bg-emerald-50 text-emerald-700 border-emerald-200",
};

const fallbackColor = "bg-slate-50 text-slate-600 border-slate-200";

export default function DomainBadge({ domain }: { domain: string }) {
	const colorClass = domainColors[domain] ?? fallbackColor;

	return (
		<span
			className={`inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium border ${colorClass}`}
		>
			{domain}
		</span>
	);
}
