declare module "react-katex" {
	import type { FC, HTMLAttributes } from "react";

	interface KaTeXProps extends HTMLAttributes<HTMLDivElement> {
		math: string;
		errorColor?: string;
		renderError?: (error: Error) => React.ReactNode;
	}

	export const BlockMath: FC<KaTeXProps>;
	export const InlineMath: FC<KaTeXProps>;
}
