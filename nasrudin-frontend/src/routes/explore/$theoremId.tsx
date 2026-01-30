import { createFileRoute } from "@tanstack/react-router";
import {
	Background,
	Controls,
	type Edge,
	Handle,
	MiniMap,
	type Node,
	type NodeProps,
	Position,
	ReactFlow,
} from "@xyflow/react";
import "@xyflow/react/dist/style.css";
import "katex/dist/katex.min.css";
import dagre from "@dagrejs/dagre";
import { useMemo } from "react";
import { BlockMath } from "react-katex";
import DomainBadge from "../../components/DomainBadge";

export const Route = createFileRoute("/explore/$theoremId")({
	component: ExploreCanvas,
});

interface TheoremNodeData {
	label: string;
	latex: string;
	domain: string;
	depth: number;
	isAxiom: boolean;
	[key: string]: unknown;
}

const nodeWidth = 280;
const nodeHeight = 130;

function getLayoutedElements(
	nodes: Node<TheoremNodeData>[],
	edges: Edge[],
): { nodes: Node<TheoremNodeData>[]; edges: Edge[] } {
	const g = new dagre.graphlib.Graph();
	g.setDefaultEdgeLabel(() => ({}));
	g.setGraph({ rankdir: "TB", nodesep: 60, ranksep: 80 });

	for (const node of nodes) {
		g.setNode(node.id, { width: nodeWidth, height: nodeHeight });
	}
	for (const edge of edges) {
		g.setEdge(edge.source, edge.target);
	}

	dagre.layout(g);

	const layoutedNodes = nodes.map((node) => {
		const nodeWithPosition = g.node(node.id);
		return {
			...node,
			position: {
				x: nodeWithPosition.x - nodeWidth / 2,
				y: nodeWithPosition.y - nodeHeight / 2,
			},
		};
	});

	return { nodes: layoutedNodes, edges };
}

function TheoremNode({ data }: NodeProps<Node<TheoremNodeData>>) {
	const borderColor = data.isAxiom ? "border-amber-300" : "border-blue-200";
	const bgColor = data.isAxiom ? "bg-amber-50" : "bg-white";

	return (
		<div
			className={`${bgColor} border ${borderColor} rounded-lg p-3 min-w-[240px] max-w-[280px] shadow-sm`}
		>
			<Handle type="target" position={Position.Top} className="!bg-slate-400" />
			<div className="overflow-x-auto mb-2 text-sm">
				<BlockMath math={data.latex} />
			</div>
			<div className="flex items-center justify-between">
				<DomainBadge domain={data.domain} />
				<span className="text-xs text-slate-500">
					{data.isAxiom ? "axiom" : `depth ${data.depth}`}
				</span>
			</div>
			<Handle
				type="source"
				position={Position.Bottom}
				className="!bg-slate-400"
			/>
		</div>
	);
}

const nodeTypes = { theorem: TheoremNode };

const initialNodes: Node<TheoremNodeData>[] = [
	{
		id: "ax-1",
		type: "theorem",
		position: { x: 0, y: 0 },
		data: {
			label: "Newton's Second Law",
			latex: "\\vec{F} = m\\vec{a}",
			domain: "Classical Mechanics",
			depth: 0,
			isAxiom: true,
		},
	},
	{
		id: "ax-2",
		type: "theorem",
		position: { x: 0, y: 0 },
		data: {
			label: "Conservation of Momentum",
			latex: "\\frac{d\\vec{p}}{dt} = 0",
			domain: "Classical Mechanics",
			depth: 0,
			isAxiom: true,
		},
	},
	{
		id: "ax-3",
		type: "theorem",
		position: { x: 0, y: 0 },
		data: {
			label: "Conservation of Energy",
			latex: "\\frac{dE}{dt} = 0",
			domain: "Classical Mechanics",
			depth: 0,
			isAxiom: true,
		},
	},
	{
		id: "thm-1",
		type: "theorem",
		position: { x: 0, y: 0 },
		data: {
			label: "Kinetic Energy",
			latex: "E_k = \\frac{1}{2}mv^2",
			domain: "Classical Mechanics",
			depth: 1,
			isAxiom: false,
		},
	},
	{
		id: "thm-2",
		type: "theorem",
		position: { x: 0, y: 0 },
		data: {
			label: "Work-Energy Theorem",
			latex: "W = \\Delta E_k = \\int \\vec{F} \\cdot d\\vec{s}",
			domain: "Classical Mechanics",
			depth: 2,
			isAxiom: false,
		},
	},
	{
		id: "thm-3",
		type: "theorem",
		position: { x: 0, y: 0 },
		data: {
			label: "Impulse-Momentum",
			latex: "\\vec{J} = \\Delta \\vec{p} = \\int \\vec{F} \\, dt",
			domain: "Classical Mechanics",
			depth: 2,
			isAxiom: false,
		},
	},
];

const initialEdges: Edge[] = [
	{ id: "e-ax1-thm1", source: "ax-1", target: "thm-1", animated: true },
	{ id: "e-ax3-thm1", source: "ax-3", target: "thm-1", animated: true },
	{ id: "e-ax1-thm2", source: "ax-1", target: "thm-2" },
	{ id: "e-thm1-thm2", source: "thm-1", target: "thm-2" },
	{ id: "e-ax1-thm3", source: "ax-1", target: "thm-3" },
	{ id: "e-ax2-thm3", source: "ax-2", target: "thm-3" },
];

function ExploreCanvas() {
	const { theoremId } = Route.useParams();

	const { nodes, edges } = useMemo(
		() => getLayoutedElements(initialNodes, initialEdges),
		[],
	);

	return (
		<div className="h-screen w-full relative bg-slate-50">
			<div className="absolute top-4 left-4 z-10 bg-white/90 border border-slate-200 rounded-lg px-4 py-2 backdrop-blur shadow-sm">
				<p className="text-sm text-slate-500">
					Exploring:{" "}
					<span className="text-slate-900 font-medium">{theoremId}</span>
				</p>
			</div>
			<ReactFlow
				nodes={nodes}
				edges={edges}
				nodeTypes={nodeTypes}
				fitView
				proOptions={{ hideAttribution: true }}
				defaultEdgeOptions={{
					style: { stroke: "#cbd5e1", strokeWidth: 2 },
				}}
			>
				<Background color="#e2e8f0" gap={20} />
				<Controls />
				<MiniMap
					style={{
						backgroundColor: "#f8fafc",
						border: "1px solid #e2e8f0",
					}}
					nodeColor={(node) => {
						const data = node.data as TheoremNodeData;
						return data.isAxiom ? "#d97706" : "#3b82f6";
					}}
					maskColor="rgba(248, 250, 252, 0.7)"
				/>
			</ReactFlow>
		</div>
	);
}
