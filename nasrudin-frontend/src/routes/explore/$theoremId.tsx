import { createFileRoute } from '@tanstack/react-router'
import {
  ReactFlow,
  Background,
  Controls,
  MiniMap,
  type Node,
  type Edge,
  type NodeProps,
  Handle,
  Position,
} from '@xyflow/react'
import '@xyflow/react/dist/style.css'
import 'katex/dist/katex.min.css'
import { BlockMath } from 'react-katex'
import dagre from '@dagrejs/dagre'
import { useMemo } from 'react'
import DomainBadge from '../../components/DomainBadge'

export const Route = createFileRoute('/explore/$theoremId')({
  component: ExploreCanvas,
})

interface TheoremNodeData {
  label: string
  latex: string
  domain: string
  depth: number
  isAxiom: boolean
  [key: string]: unknown
}

const nodeWidth = 280
const nodeHeight = 130

function getLayoutedElements(
  nodes: Node<TheoremNodeData>[],
  edges: Edge[],
): { nodes: Node<TheoremNodeData>[]; edges: Edge[] } {
  const g = new dagre.graphlib.Graph()
  g.setDefaultEdgeLabel(() => ({}))
  g.setGraph({ rankdir: 'TB', nodesep: 60, ranksep: 80 })

  for (const node of nodes) {
    g.setNode(node.id, { width: nodeWidth, height: nodeHeight })
  }
  for (const edge of edges) {
    g.setEdge(edge.source, edge.target)
  }

  dagre.layout(g)

  const layoutedNodes = nodes.map((node) => {
    const nodeWithPosition = g.node(node.id)
    return {
      ...node,
      position: {
        x: nodeWithPosition.x - nodeWidth / 2,
        y: nodeWithPosition.y - nodeHeight / 2,
      },
    }
  })

  return { nodes: layoutedNodes, edges }
}

function TheoremNode({ data }: NodeProps<Node<TheoremNodeData>>) {
  const borderColor = data.isAxiom ? 'border-amber-500/60' : 'border-blue-500/40'
  const bgColor = data.isAxiom ? 'bg-amber-950/30' : 'bg-zinc-900'

  return (
    <div
      className={`${bgColor} border ${borderColor} rounded-lg p-3 min-w-[240px] max-w-[280px] shadow-lg`}
    >
      <Handle type="target" position={Position.Top} className="!bg-zinc-600" />
      <div className="overflow-x-auto mb-2 text-sm">
        <BlockMath math={data.latex} />
      </div>
      <div className="flex items-center justify-between">
        <DomainBadge domain={data.domain} />
        <span className="text-xs text-zinc-500">
          {data.isAxiom ? 'axiom' : `depth ${data.depth}`}
        </span>
      </div>
      <Handle
        type="source"
        position={Position.Bottom}
        className="!bg-zinc-600"
      />
    </div>
  )
}

const nodeTypes = { theorem: TheoremNode }

const initialNodes: Node<TheoremNodeData>[] = [
  {
    id: 'ax-1',
    type: 'theorem',
    position: { x: 0, y: 0 },
    data: {
      label: "Newton's Second Law",
      latex: '\\vec{F} = m\\vec{a}',
      domain: 'Classical Mechanics',
      depth: 0,
      isAxiom: true,
    },
  },
  {
    id: 'ax-2',
    type: 'theorem',
    position: { x: 0, y: 0 },
    data: {
      label: 'Conservation of Momentum',
      latex: '\\frac{d\\vec{p}}{dt} = 0',
      domain: 'Classical Mechanics',
      depth: 0,
      isAxiom: true,
    },
  },
  {
    id: 'ax-3',
    type: 'theorem',
    position: { x: 0, y: 0 },
    data: {
      label: 'Conservation of Energy',
      latex: '\\frac{dE}{dt} = 0',
      domain: 'Classical Mechanics',
      depth: 0,
      isAxiom: true,
    },
  },
  {
    id: 'thm-1',
    type: 'theorem',
    position: { x: 0, y: 0 },
    data: {
      label: 'Kinetic Energy',
      latex: 'E_k = \\frac{1}{2}mv^2',
      domain: 'Classical Mechanics',
      depth: 1,
      isAxiom: false,
    },
  },
  {
    id: 'thm-2',
    type: 'theorem',
    position: { x: 0, y: 0 },
    data: {
      label: 'Work-Energy Theorem',
      latex: 'W = \\Delta E_k = \\int \\vec{F} \\cdot d\\vec{s}',
      domain: 'Classical Mechanics',
      depth: 2,
      isAxiom: false,
    },
  },
  {
    id: 'thm-3',
    type: 'theorem',
    position: { x: 0, y: 0 },
    data: {
      label: 'Impulse-Momentum',
      latex: '\\vec{J} = \\Delta \\vec{p} = \\int \\vec{F} \\, dt',
      domain: 'Classical Mechanics',
      depth: 2,
      isAxiom: false,
    },
  },
]

const initialEdges: Edge[] = [
  { id: 'e-ax1-thm1', source: 'ax-1', target: 'thm-1', animated: true },
  { id: 'e-ax3-thm1', source: 'ax-3', target: 'thm-1', animated: true },
  { id: 'e-ax1-thm2', source: 'ax-1', target: 'thm-2' },
  { id: 'e-thm1-thm2', source: 'thm-1', target: 'thm-2' },
  { id: 'e-ax1-thm3', source: 'ax-1', target: 'thm-3' },
  { id: 'e-ax2-thm3', source: 'ax-2', target: 'thm-3' },
]

function ExploreCanvas() {
  const { theoremId } = Route.useParams()

  const { nodes, edges } = useMemo(
    () => getLayoutedElements(initialNodes, initialEdges),
    [],
  )

  return (
    <div className="h-screen w-full relative">
      <div className="absolute top-4 left-4 z-10 bg-zinc-900/90 border border-zinc-800 rounded-lg px-4 py-2 backdrop-blur">
        <p className="text-sm text-zinc-400">
          Exploring: <span className="text-zinc-200 font-medium">{theoremId}</span>
        </p>
      </div>
      <ReactFlow
        nodes={nodes}
        edges={edges}
        nodeTypes={nodeTypes}
        fitView
        proOptions={{ hideAttribution: true }}
        defaultEdgeOptions={{
          style: { stroke: '#3f3f46', strokeWidth: 2 },
        }}
      >
        <Background color="#27272a" gap={20} />
        <Controls
          className="!bg-zinc-900 !border-zinc-800 !shadow-lg [&>button]:!bg-zinc-800 [&>button]:!border-zinc-700 [&>button]:!text-zinc-300 [&>button:hover]:!bg-zinc-700"
        />
        <MiniMap
          style={{
            backgroundColor: '#09090b',
            border: '1px solid #27272a',
          }}
          nodeColor={(node) => {
            const data = node.data as TheoremNodeData
            return data.isAxiom ? '#d97706' : '#3b82f6'
          }}
          maskColor="rgba(0, 0, 0, 0.7)"
        />
      </ReactFlow>
    </div>
  )
}
