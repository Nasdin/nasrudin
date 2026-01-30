# LLM Integration: Guided Bottom-Up Discovery

## The Core Insight

The system is **bottom-up** — it starts from axioms and builds upward. Existing
LLM provers (AlphaProof, Goedel-Prover) are **top-down** — given a target
theorem, they find a proof. These are complementary, not competing.

The LLM does NOT know what E=mc² is. It does NOT set goals. Instead, it serves
three roles that make the blind GA into an **informed** GA:

```
                    Without LLM                    With LLM
                    ─────────────                  ──────────────
Crossover:          Random subtree swap            LLM suggests which subtrees
                                                   are worth combining
Mutation:           Random operator change          LLM proposes semantically
                                                   meaningful mutations
Fitness:            Dimensional analysis +          + LLM scores "does this look
                    symmetry + complexity           like real physics?"
Tactic selection:   Try all 8 in sequence           LLM predicts which tactic
                                                   will work (10x faster)
Exploration:        Uniform random                  LLM identifies promising
                                                   regions of theorem space
```

This is the **FunSearch pattern** (DeepMind, 2024): LLM as a learned mutation
operator inside an evolutionary loop. Their system discovered new mathematical
results (cap set bounds) that humans hadn't found.

---

## Three Layers of LLM Integration

### Layer 1: LLM-Guided Genetic Operators (FunSearch Pattern)

Replace random GA operators with LLM-informed ones. The LLM is a **frozen
model called via API** — no training needed.

```
┌──────────────────────────────────────────────────────┐
│                 GA Generation Loop                    │
│                                                       │
│  1. Select parents (tournament selection)             │
│  2. Ask LLM: "Given these two theorems, suggest       │
│     a promising way to combine them"                  │
│  3. LLM returns candidate combination                 │
│  4. Dimensional analysis filter                       │
│  5. Lean4 verification                                │
│  6. If verified → score fitness → store               │
│  7. Feed best results back to LLM context             │
│                                                       │
│  Fallback: If LLM is slow/unavailable, use random    │
│  crossover (pure GA mode still works)                │
└──────────────────────────────────────────────────────┘
```

**Prompt template for crossover suggestion:**

```
You are a mathematical physicist. Given these two verified theorems:

Theorem A (Special Relativity, depth 3):
  The spacetime interval s² = c²t² - x² - y² - z² is invariant
  under Lorentz transformations.

Theorem B (Classical Mechanics, depth 1):
  For a closed system, total momentum p = Σ mᵢvᵢ is conserved.

Using only standard mathematical operations (substitution, algebraic
manipulation, limit-taking, differentiation, integration), suggest
3 candidate theorems that could be derived by combining A and B.

Output each as a proposition in canonical prefix notation.
Do NOT use any physics knowledge beyond what is stated in A and B.
```

**Why this works bottom-up:** The LLM never sees a target. It only sees
existing theorems and proposes combinations. It's a learned heuristic for
"what combinations are structurally promising" — trained on all of physics
and math literature, but constrained to only use what the system has proven.

**Throughput model:**
- Pure GA: 1000 candidates/sec (random, most rejected)
- LLM-guided: 10 candidates/sec (each one is high quality)
- Hybrid: 900 random + 100 LLM-guided per second
- The 100 LLM-guided candidates will have ~10x higher verification rate

### Layer 2: LLM-Guided Tactic Selection

Instead of trying all 8 Lean4 tactics in sequence (omega → norm_num → ring →
simp → linarith → field_simp → polyrith → grind), the LLM predicts which
tactic is most likely to succeed. This is exactly what AlphaProof's policy
network does, but we use a frozen LLM instead of training one.

```
┌───────────────────────────────────────────────┐
│           Lean4 Verification Pipeline          │
│                                                │
│  Candidate arrives                             │
│       │                                        │
│  ┌────▼────┐   "This is a polynomial          │
│  │  LLM    │    equality → try ring first,     │
│  │ Tactic  │    then polyrith"                 │
│  │ Advisor │                                   │
│  └────┬────┘                                   │
│       │ ordered tactic list                    │
│       ▼                                        │
│  Try tactics in LLM-suggested order            │
│  (with timeouts)                               │
│       │                                        │
│  Result: verified / rejected / timeout         │
└───────────────────────────────────────────────┘
```

**Impact:** If the LLM correctly predicts the right tactic as its first choice
50% of the time, average verification time drops from ~10s to ~2s. This 5x
speedup means 5x more theorems verified per hour.

**Prompt template:**

```
Given this Lean4 goal:
  ⊢ ∀ (m : ℝ) (v : ℝ), m * v * v / 2 = (1/2) * m * v ^ 2

Which Lean4 tactic is most likely to close this goal?
Choose from: omega, norm_num, ring, simp, linarith, field_simp, polyrith, grind

Return a ranked list of the top 3 tactics.
```

### Layer 3: LLM as Exploration Curator (Novel)

This is the **genuinely new** idea. The LLM periodically reviews the theorem
database and identifies:

1. **Gaps**: "You have Lorentz transformations and energy conservation, but
   nothing combining them. This region of theorem space is underexplored."
2. **Clusters**: "These 50 theorems are all trivial variants of each other.
   Reduce fitness for this cluster."
3. **Analogies**: "This pattern in electromagnetism is structurally similar to
   this pattern in fluid dynamics. Cross-domain combination is promising."
4. **Promising directions**: "You're 2 steps away from deriving the wave
   equation from Maxwell's equations. Prioritize EM-domain exploration."

```
┌───────────────────────────────────────────────────────┐
│              LLM Exploration Curator                   │
│              (runs every N generations)                 │
│                                                        │
│  Input: Summary of recent theorem database state       │
│    - Domain distribution                               │
│    - Recent high-fitness discoveries                   │
│    - Underexplored axiom combinations                  │
│    - Largest connected components in lineage graph      │
│                                                        │
│  Output: Exploration directives                        │
│    - Adjust island weights (more resources to EM)      │
│    - Seed new axiom combinations to try                │
│    - Adjust fitness weights (reward cross-domain)      │
│    - Flag promising near-miss candidates for retry     │
│                                                        │
│  Does NOT set target theorems.                         │
│  Only adjusts WHERE the GA focuses its search.         │
└───────────────────────────────────────────────────────┘
```

**This is bottom-up because:** The curator never says "find E=mc²." It says
"the intersection of SR and conservation laws is underexplored — allocate more
compute there." The GA still discovers what it discovers.

---

## MCP Architecture

MCP (Model Context Protocol) is the interface between the LLM and the system.
The LLM calls tools via MCP to read theorems, suggest combinations, and
guide exploration.

### MCP Server: `physics-generator-mcp`

Runs as a sidecar process alongside the Rust engine. Exposes tools:

```typescript
// MCP Tool Definitions

// ── Theorem Database Tools ──────────────────────────────

tool("search_theorems", {
  description: "Search for theorems by LaTeX, domain, or canonical form",
  parameters: {
    query: string,        // LaTeX or canonical prefix notation
    domain: Domain?,      // Filter by physics domain
    min_depth: number?,   // Minimum derivation depth
    max_depth: number?,   // Maximum derivation depth
    limit: number?,       // Max results (default 10)
  },
  returns: TheoremResponse[]
})

tool("get_theorem", {
  description: "Get a theorem by ID with full proof tree",
  parameters: { id: string },
  returns: { theorem: TheoremResponse, proof: ProofTree }
})

tool("get_lineage", {
  description: "Get parent and child theorems (derivation graph)",
  parameters: {
    id: string,
    depth: number?,       // How many levels to traverse (default 2)
  },
  returns: LineageResponse
})

tool("get_axioms", {
  description: "List all seed axioms, optionally filtered by domain",
  parameters: { domain: Domain? },
  returns: TheoremResponse[]
})

tool("get_stats", {
  description: "Get engine statistics: counts, rates, domain distribution",
  returns: StatsResponse
})

tool("get_underexplored", {
  description: "Find axiom pairs that have never been combined",
  parameters: { domain: Domain?, limit: number? },
  returns: { axiom_a: TheoremResponse, axiom_b: TheoremResponse }[]
})

// ── GA Engine Tools ─────────────────────────────────────

tool("suggest_combination", {
  description: "Submit a candidate theorem for verification. The candidate " +
    "is a proposition in canonical prefix notation that the system will " +
    "attempt to verify with Lean4.",
  parameters: {
    canonical: string,     // Prefix notation expression
    parent_ids: string[],  // Which theorems this derives from
    reasoning: string,     // Why this combination is promising
  },
  returns: {
    status: "verified" | "rejected" | "timeout",
    theorem_id: string?,   // If verified
    tactic_used: string?,  // Which Lean4 tactic succeeded
  }
})

tool("adjust_exploration", {
  description: "Adjust GA exploration weights for a domain or axiom set",
  parameters: {
    domain: Domain?,           // Boost/reduce this domain
    weight_multiplier: number, // >1 = more exploration, <1 = less
    reason: string,
  },
  returns: { applied: boolean }
})

tool("flag_near_miss", {
  description: "Flag a rejected candidate for retry with modifications",
  parameters: {
    canonical: string,     // The rejected candidate
    suggestion: string,    // What to modify
  },
  returns: { queued: boolean }
})

// ── Lean4 Tools ─────────────────────────────────────────

tool("check_type", {
  description: "Type-check an expression without full proof (fast)",
  parameters: { canonical: string },
  returns: { well_typed: boolean, type: string?, error: string? }
})

tool("simplify", {
  description: "Simplify an expression using Lean4 simp",
  parameters: { canonical: string },
  returns: { simplified: string, changed: boolean }
})

tool("predict_tactic", {
  description: "Given a Lean4 goal, predict which tactic will work",
  parameters: { goal: string },
  returns: { tactics: { name: string, confidence: number }[] }
})
```

### MCP Integration Architecture

```
┌──────────────────────────────────────────────────────────────┐
│                        LLM (Claude/GPT)                       │
│                                                               │
│  Called periodically or on-demand via API                     │
│  System prompt: "You are a mathematical physics curator..."   │
│                                                               │
│  Available MCP tools:                                         │
│    search_theorems, get_lineage, get_underexplored,          │
│    suggest_combination, adjust_exploration, simplify, ...     │
└──────────────┬───────────────────────────────────────────────┘
               │ MCP protocol (JSON-RPC over stdio/SSE)
┌──────────────▼───────────────────────────────────────────────┐
│                    MCP Server (Rust)                           │
│                                                               │
│  Translates MCP tool calls to:                               │
│    • RocksDB reads (search, get, lineage)                    │
│    • GA engine commands (suggest, adjust weights)            │
│    • Lean4 FFI calls (type-check, simplify)                  │
│                                                               │
│  Runs as sidecar: same process or unix socket to engine       │
└──────────────┬───────────────────────────────────────────────┘
               │
    ┌──────────┴──────────┐
    │                     │
┌───▼───┐          ┌──────▼──────┐
│RocksDB│          │ Rust Engine │
│       │          │ + Lean4     │
└───────┘          └─────────────┘
```

### Orchestration Modes

**Mode 1: Curator Loop (periodic, async)**

Runs every K generations. The LLM reviews the state and adjusts strategy.

```python
# Pseudocode for curator loop
async def curator_loop():
    while True:
        await wait_for_generations(K=100)

        # 1. Gather state
        stats = await mcp.call("get_stats")
        underexplored = await mcp.call("get_underexplored", limit=20)
        recent = await mcp.call("search_theorems", query="*",
                                 min_depth=stats.max_depth - 2, limit=50)

        # 2. LLM analyzes and acts
        response = await llm.chat([
            system_prompt,
            f"Current state: {stats.total_theorems} theorems, "
            f"generation {stats.generation}. "
            f"Domain distribution: {stats.domain_counts}. "
            f"These axiom pairs have never been combined: {underexplored}. "
            f"Recent high-fitness discoveries: {recent}. "
            f"What exploration adjustments would you recommend? "
            f"Use your tools to implement them."
        ])
        # LLM calls adjust_exploration, suggest_combination, etc.
```

**Mode 2: Inline Crossover (synchronous, per-candidate)**

For high-value candidates, the LLM suggests the crossover directly.

```python
# Called for top 10% of tournament-selected parents
async def llm_crossover(parent_a, parent_b):
    response = await llm.chat([
        "Given these two proven theorems, suggest a derivation "
        "that combines them. Use suggest_combination to submit.",
        f"Theorem A: {parent_a.latex}",
        f"Theorem B: {parent_b.latex}",
    ])
    # LLM calls suggest_combination tool
    return response.tool_results
```

**Mode 3: Tactic Advisor (synchronous, per-verification)**

LLM predicts the right tactic before Lean4 tries them all.

```python
async def advised_verify(candidate):
    prediction = await llm.chat([
        f"Which Lean4 tactic will prove: {candidate.canonical}?",
        "Return ranked list: [tactic_name, confidence]"
    ])
    # Try tactics in predicted order instead of fixed sequence
    for tactic in prediction.ranked_tactics:
        result = lean4.try_tactic(candidate, tactic)
        if result.success:
            return result
```

---

## Hybrid Architecture: GA + LLM

The system runs both in parallel. The GA is the workhorse (high throughput,
random exploration). The LLM is the advisor (low throughput, high quality).

```
Throughput budget per second:
┌──────────────────────────────────────────────────┐
│                                                   │
│  ████████████████████████████████  900 random GA  │
│  ██████████                       100 LLM-guided  │
│                                                   │
│  Random: ~2% verification rate → 18 theorems/sec  │
│  LLM:    ~20% verification rate → 20 theorems/sec │
│                                                   │
│  LLM produces same output with 10x fewer tries    │
└──────────────────────────────────────────────────┘
```

The LLM is **not in the critical path**. If the LLM API is down or slow,
the system degrades gracefully to pure GA mode. The LLM is an accelerator,
not a dependency.

---

## What's Genuinely Novel Here

Existing systems (AlphaProof, Goedel-Prover) are **top-down**: given a theorem
to prove, find the proof. They require a target.

This system is **bottom-up with LLM curation**: no target, the LLM guides
where to explore, not what to find. This is closer to FunSearch/AlphaEvolve
but applied to physics theorem space rather than optimization problems.

| System | Direction | LLM Role | Target Required? |
|--------|-----------|----------|-----------------|
| AlphaProof | Top-down | Policy + value network | Yes (IMO problem) |
| Goedel-Prover | Top-down | Proof generator | Yes (theorem statement) |
| FunSearch | Bottom-up | Mutation operator | No (fitness function) |
| **This system** | **Bottom-up** | **Curator + crossover + tactic advisor** | **No** |

The innovation is the **curator role**: an LLM that reads the evolving theorem
database and steers exploration toward fertile regions of physics space, without
ever being told what it should find. It discovers what's interesting by
recognizing structural patterns across domains.

---

## Implementation Priority

| Phase | LLM Feature | Complexity | Impact |
|-------|-------------|------------|--------|
| 1 | Tactic advisor (predict which Lean4 tactic) | Low | 5x verification speedup |
| 2 | LLM-guided crossover (FunSearch pattern) | Medium | 10x candidate quality |
| 3 | MCP server with full tool suite | Medium | Enables all LLM modes |
| 4 | Curator loop (periodic exploration guidance) | High | Strategic exploration |
| 5 | Adaptive LLM (fine-tune on system's own discoveries) | Very high | Self-improving |

Start with Phase 1 — it's the lowest-hanging fruit and doesn't require MCP.
Just call the LLM API with the goal string and parse the tactic prediction.

---

## Cost Model

| Mode | Calls/hour | Tokens/call | Cost/hour (Claude Sonnet) |
|------|-----------|-------------|---------------------------|
| Tactic advisor | 3,600 | ~200 | ~$2.16 |
| LLM crossover (10%) | 360 | ~500 | ~$0.54 |
| Curator loop | 1 | ~5,000 | ~$0.02 |
| **Total** | **~3,961** | | **~$2.72/hour** |

At $2.72/hour, the LLM guidance costs less than the compute for Lean4
verification. The ROI is massive if it even doubles the discovery rate.
