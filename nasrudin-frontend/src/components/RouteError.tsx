export function RouteError({
	error,
	reset,
}: {
	error: Error;
	reset: () => void;
}) {
	return (
		<div className="p-8 max-w-xl mx-auto text-center">
			<h2 className="text-xl font-bold text-slate-900 mb-2">
				Something went wrong
			</h2>
			<p className="text-sm text-slate-500 mb-4">{error.message}</p>
			<button
				type="button"
				onClick={reset}
				className="text-sm text-blue-700 hover:underline"
			>
				Try again
			</button>
		</div>
	);
}
