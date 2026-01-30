import { Link, useRouterState } from "@tanstack/react-router";

const navItems = [
	{ to: "/domains" as const, label: "Domains" },
	{ to: "/axioms" as const, label: "Axioms" },
	{ to: "/timeline" as const, label: "Timeline" },
	{ to: "/engine" as const, label: "Engine" },
];

export default function TopNav() {
	const routerState = useRouterState();
	const currentPath = routerState.location.pathname;

	return (
		<header className="sticky top-0 z-40 w-full border-b border-slate-200 bg-white/80 backdrop-blur">
			<div className="mx-auto flex h-14 max-w-7xl items-center justify-between px-6">
				<Link
					to="/"
					className="text-lg font-bold text-slate-900 tracking-tight"
				>
					Nasrudin
				</Link>

				<nav className="flex items-center gap-1">
					{navItems.map((item) => {
						const isActive = currentPath.startsWith(item.to);

						return (
							<Link
								key={item.to}
								to={item.to}
								className={`px-3 py-1.5 rounded-md text-sm font-medium transition-colors ${
									isActive
										? "bg-slate-100 text-slate-900"
										: "text-slate-600 hover:text-slate-900 hover:bg-slate-50"
								}`}
							>
								{item.label}
							</Link>
						);
					})}

					<div className="ml-4 pl-4 border-l border-slate-200">
						<span className="px-3 py-1.5 text-sm font-medium text-slate-500 cursor-default">
							Login
						</span>
					</div>
				</nav>
			</div>
		</header>
	);
}
