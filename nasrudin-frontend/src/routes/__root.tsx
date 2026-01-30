import {
	createRootRoute,
	HeadContent,
	Outlet,
	Scripts,
} from "@tanstack/react-router";

import TopNav from "../components/TopNav";

import appCss from "../styles.css?url";

export const Route = createRootRoute({
	head: () => ({
		meta: [
			{
				charSet: "utf-8",
			},
			{
				name: "viewport",
				content: "width=device-width, initial-scale=1",
			},
			{
				title: "Nasrudin — Formally Verified Physics Theorems",
			},
		],
		links: [
			{
				rel: "stylesheet",
				href: appCss,
			},
			{
				rel: "stylesheet",
				href: "https://cdn.jsdelivr.net/npm/katex@0.16.28/dist/katex.min.css",
			},
		],
	}),

	shellComponent: RootDocument,
	component: RootLayout,
});

function RootDocument({ children }: { children: React.ReactNode }) {
	return (
		<html lang="en">
			<head>
				<HeadContent />
			</head>
			<body className="bg-white text-slate-900 antialiased">
				{children}
				<Scripts />
			</body>
		</html>
	);
}

function RootLayout() {
	return (
		<div className="flex min-h-screen flex-col">
			<TopNav />
			<main className="flex-1">
				<Outlet />
			</main>
			<footer className="border-t border-slate-200 bg-slate-50 py-6 text-center text-sm text-slate-500">
				<p>
					Created by{" "}
					<a
						href="https://nasrudinsalim.com"
						target="_blank"
						rel="noopener noreferrer"
						className="text-slate-700 underline hover:text-slate-900"
					>
						Nasrudin Salim
					</a>{" "}
					&middot;{" "}
					<a
						href="mailto:mail@nasrudinsalim.com"
						className="text-slate-700 underline hover:text-slate-900"
					>
						mail@nasrudinsalim.com
					</a>
				</p>
			</footer>
		</div>
	);
}
