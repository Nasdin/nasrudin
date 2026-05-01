import { memo } from 'react';

function PipelineSteering() {
  return (
    <svg viewBox="0 0 600 80" width="100%" height="80" style={{ display: 'block' }}>
      <title>LLM steerer + reinforcement-learning bandits</title>
      <defs>
        <marker
          id="arr-steer"
          viewBox="0 0 10 10"
          refX="9"
          refY="5"
          markerWidth="6"
          markerHeight="6"
          orient="auto"
        >
          <path d="M0,0 L10,5 L0,10 z" fill="var(--terracotta-500)" />
        </marker>
      </defs>

      {/* LLM box on the left */}
      <rect
        x="20"
        y="22"
        width="92"
        height="36"
        rx="6"
        fill="var(--ink-900)"
        stroke="var(--ink-900)"
      />
      <text
        x="66"
        y="38"
        textAnchor="middle"
        fontSize="10"
        fill="var(--paper-50)"
        fontFamily="var(--font-mono)"
        fontWeight="600"
      >
        LLM
      </text>
      <text
        x="66"
        y="51"
        textAnchor="middle"
        fontSize="9"
        fill="var(--paper-200)"
        fontFamily="var(--font-mono)"
      >
        Kimi K2.5
      </text>

      {/* Three bandit chips on the right */}
      {(['UCB1 K', 'directive', 'compute'] as const).map((label, i) => (
        <g key={label}>
          <rect
            x={250 + i * 100}
            y="14"
            width="86"
            height="22"
            rx="4"
            fill="var(--olive-50)"
            stroke="var(--olive-500)"
            strokeWidth="0.8"
          />
          <text
            x={293 + i * 100}
            y="29"
            textAnchor="middle"
            fontSize="10"
            fill="var(--olive-700)"
            fontFamily="var(--font-mono)"
          >
            {label}
          </text>
        </g>
      ))}
      <text x="250" y="50" fontSize="9" fill="var(--ink-500)" fontFamily="var(--font-mono)">
        UCB1 + LinUCB · γ=0.7 traces · novelty bonus
      </text>

      {/* Arrow LLM → bandits */}
      <line
        x1="112"
        y1="35"
        x2="246"
        y2="25"
        stroke="var(--terracotta-500)"
        strokeWidth="1.4"
        markerEnd="url(#arr-steer)"
      >
        <animate attributeName="opacity" values="0.4;1;0.4" dur="2.6s" repeatCount="indefinite" />
      </line>

      {/* Reward feedback loop bottom */}
      <path
        d="M 580 70 Q 320 75 60 70"
        fill="none"
        stroke="var(--olive-500)"
        strokeWidth="1.2"
        strokeDasharray="3 3"
        markerEnd="url(#arr-steer)"
      >
        <animate
          attributeName="stroke-dashoffset"
          values="0;-12"
          dur="1.5s"
          repeatCount="indefinite"
        />
      </path>
      <text
        x="320"
        y="68"
        textAnchor="middle"
        fontSize="9"
        fill="var(--olive-700)"
        fontFamily="var(--font-mono)"
      >
        reward feedback
      </text>
    </svg>
  );
}

function PipelineSeed() {
  const dots = Array.from({ length: 28 });
  return (
    <svg viewBox="0 0 600 80" width="100%" height="80" style={{ display: 'block' }}>
      <title>Mathematical axiom seeds</title>
      {dots.map((_, i) => {
        const x = (i % 14) * 40 + 24;
        const y = Math.floor(i / 14) * 32 + 22;
        return (
          <g key={`${x}-${y}`}>
            <circle
              cx={x}
              cy={y}
              r="3.2"
              fill="var(--terracotta-500)"
              opacity={0.55 - (i % 3) * 0.1}
            >
              <animate
                attributeName="opacity"
                values="0.2;0.7;0.2"
                dur={`${2 + (i % 5) * 0.3}s`}
                repeatCount="indefinite"
                begin={`${(i % 7) * 0.2}s`}
              />
            </circle>
          </g>
        );
      })}
      <text
        x="580"
        y="46"
        textAnchor="end"
        fontSize="10"
        fill="var(--ink-400)"
        fontFamily="var(--font-mono)"
      >
        axioms
      </text>
    </svg>
  );
}

function PipelineGA() {
  return (
    <svg viewBox="0 0 600 80" width="100%" height="80" style={{ display: 'block' }}>
      <title>GA mutation and crossover</title>
      <defs>
        <marker
          id="arr1"
          viewBox="0 0 10 10"
          refX="9"
          refY="5"
          markerWidth="6"
          markerHeight="6"
          orient="auto"
        >
          <path d="M0,0 L10,5 L0,10 z" fill="var(--terracotta-500)" />
        </marker>
      </defs>
      {[0, 1, 2].map((r) => (
        <g key={r}>
          <circle cx="80" cy={20 + r * 20} r="4" fill="var(--terracotta-300)" />
          <circle cx="180" cy={20 + r * 20} r="4" fill="var(--terracotta-300)" />
          <line
            x1="84"
            y1={20 + r * 20}
            x2="176"
            y2={20 + r * 20}
            stroke="var(--paper-300)"
            strokeDasharray="2 3"
            strokeWidth="1"
          />
        </g>
      ))}
      {/* crossover lines */}
      <line
        x1="180"
        y1="20"
        x2="320"
        y2="40"
        stroke="var(--terracotta-500)"
        strokeWidth="1.4"
        markerEnd="url(#arr1)"
      >
        <animate attributeName="opacity" values="0.3;1;0.3" dur="2.4s" repeatCount="indefinite" />
      </line>
      <line
        x1="180"
        y1="60"
        x2="320"
        y2="40"
        stroke="var(--terracotta-500)"
        strokeWidth="1.4"
        markerEnd="url(#arr1)"
      >
        <animate
          attributeName="opacity"
          values="0.3;1;0.3"
          dur="2.4s"
          repeatCount="indefinite"
          begin="0.4s"
        />
      </line>
      <circle cx="320" cy="40" r="6" fill="var(--terracotta-700)" />
      <text x="340" y="36" fontSize="11" fill="var(--ink-700)" fontFamily="var(--font-mono)">
        mutate
      </text>
      <text x="340" y="50" fontSize="11" fill="var(--ink-700)" fontFamily="var(--font-mono)">
        crossover
      </text>
      <line
        x1="430"
        y1="40"
        x2="580"
        y2="40"
        stroke="var(--ink-300)"
        strokeWidth="1"
        markerEnd="url(#arr1)"
      />
    </svg>
  );
}

function PipelineCandidates() {
  return (
    <svg viewBox="0 0 600 80" width="100%" height="80" style={{ display: 'block' }}>
      <title>Candidate theorem stream</title>
      {Array.from({ length: 18 }).map((_, i) => {
        const x = i * 32 + 16;
        const ok = i % 4 === 1 || i % 5 === 0;
        return (
          <g key={`cand-${x}`}>
            <rect
              x={x}
              y="22"
              width="22"
              height="36"
              rx="3"
              fill={ok ? 'var(--olive-100)' : 'var(--paper-200)'}
              stroke={ok ? 'var(--olive-500)' : 'var(--paper-300)'}
              strokeWidth="0.8"
            >
              <animate
                attributeName="y"
                values="22;18;22"
                dur={`${1.6 + (i % 3) * 0.3}s`}
                repeatCount="indefinite"
                begin={`${(i % 5) * 0.15}s`}
              />
            </rect>
          </g>
        );
      })}
      <text
        x="580"
        y="46"
        textAnchor="end"
        fontSize="10"
        fill="var(--ink-400)"
        fontFamily="var(--font-mono)"
      >
        ~14M/day
      </text>
    </svg>
  );
}

interface PipelineDiagramProps {
  totalAxioms: number;
  totalVerified: number;
  acceptanceRate: string;
}

function PipelineDB({ totalVerified }: { totalVerified: number }) {
  return (
    <svg viewBox="0 0 600 80" width="100%" height="80" style={{ display: 'block' }}>
      <title>RocksDB corpus</title>
      {[0, 1, 2].map((i) => (
        <g key={i} transform={`translate(${i * 70}, 0)`}>
          <ellipse
            cx="60"
            cy="22"
            rx="44"
            ry="6"
            fill="var(--paper-100)"
            stroke="var(--paper-300)"
          />
          <path
            d="M16,22 L16,58 A44,6 0 0 0 104,58 L104,22"
            fill="var(--paper-50)"
            stroke="var(--paper-300)"
          />
          <ellipse
            cx="60"
            cy="40"
            rx="44"
            ry="6"
            fill="none"
            stroke="var(--paper-300)"
            strokeDasharray="2 2"
          />
        </g>
      ))}
      <text x="320" y="44" fontSize="11" fill="var(--ink-700)" fontFamily="var(--font-mono">
        RocksDB · {totalVerified.toLocaleString()} verified
      </text>
      <line x1="500" y1="42" x2="580" y2="42" stroke="var(--ink-300)" strokeWidth="1" />
      <circle cx="580" cy="42" r="3" fill="var(--olive-500)" />
    </svg>
  );
}

function PipelineLean({ acceptanceRate }: { acceptanceRate: string }) {
  return (
    <svg viewBox="0 0 600 80" width="100%" height="80" style={{ display: 'block' }}>
      <title>Lean 4 verification</title>
      <rect x="20" y="24" width="220" height="34" rx="6" fill="var(--ink-900)" />
      <text x="32" y="46" fontSize="11" fill="var(--paper-50)" fontFamily="var(--font-mono)">
        by simp; ring; linarith
      </text>
      <line x1="240" y1="41" x2="320" y2="41" stroke="var(--ink-300)" strokeWidth="1" />
      <circle
        cx="350"
        cy="41"
        r="14"
        fill="var(--olive-50)"
        stroke="var(--olive-500)"
        strokeWidth="1.4"
      />
      <path
        d="M344 41 L348 45 L356 37"
        stroke="var(--olive-700)"
        strokeWidth="1.6"
        fill="none"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
      <text
        x="376"
        y="38"
        fontSize="11"
        fill="var(--olive-700)"
        fontFamily="var(--font-mono)"
        fontWeight="600"
      >
        QED
      </text>
      <text x="376" y="52" fontSize="10" fill="var(--ink-500)" fontFamily="var(--font-mono">
        accept-rate ≈ {acceptanceRate}%
      </text>
      <line
        x1="450"
        y1="41"
        x2="580"
        y2="41"
        stroke="var(--ink-300)"
        strokeWidth="1"
        strokeDasharray="2 3"
      />
    </svg>
  );
}

export const PipelineDiagram = memo(function PipelineDiagram({
  totalAxioms,
  totalVerified,
  acceptanceRate,
}: PipelineDiagramProps) {
  const stages = [
    {
      name: 'Mathematical axioms',
      sub: `${totalAxioms.toLocaleString()} from Mathlib · physics postulates`,
      viz: <PipelineSeed />,
    },
    {
      name: 'LLM steerer + RL bandits',
      sub: 'Kimi K2.5 emits intent · 4 online bandits learn the knobs',
      viz: <PipelineSteering />,
    },
    { name: 'Rust GA engine', sub: 'combine · mutate · crossover', viz: <PipelineGA /> },
    {
      name: 'Candidate theorems',
      sub: '~14M/day across the network',
      viz: <PipelineCandidates />,
    },
    {
      name: 'Lean 4 verification',
      sub: 'grind · simp · omega · ring · linarith',
      viz: <PipelineLean acceptanceRate={acceptanceRate} />,
    },
    {
      name: 'RocksDB · global corpus',
      sub: 'server re-verifies before accepting',
      viz: <PipelineDB totalVerified={totalVerified} />,
    },
  ];
  return (
    <div className="pipeline">
      {stages.map((s, i) => (
        <div className="pipe-row" key={s.name}>
          <div className="pipe-stage">
            <span className="pipe-stage-num">{String(i + 1).padStart(2, '0')}</span>
            <span>
              <span className="pipe-stage-name">{s.name}</span>
              <span className="pipe-stage-sub">{s.sub}</span>
            </span>
          </div>
          <div className="pipe-viz">{s.viz}</div>
        </div>
      ))}
    </div>
  );
});
