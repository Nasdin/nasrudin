# Frontend Architecture

## Design Philosophy

Nasrudin is a tool for exploring formally verified physics theorems. The UI
prioritizes **immediate utility**: a visitor lands, searches for a theorem,
clicks a result, and is inside an interactive derivation graph within seconds.

**Principles:**
1. **Search-first** — the landing page IS the search experience, not a stats dashboard
2. **One click to graph** — every theorem result links directly to its React Flow lineage
3. **Public utility** — no login required to search, browse, or explore graphs
4. **Technical details are opt-in** — engine stats, worker dashboards, and architecture live on a dedicated page, not the homepage

---

## Stack

| Technology | Version | Purpose |
|-----------|---------|---------|
| TanStack Start | v1 RC | Full-stack React framework |
| TanStack Router | v1 | Type-safe file-based routing |
| TanStack Query | v5 | Server state management, caching |
| React Flow (@xyflow/react) | v12 | Node graph canvas |
| KaTeX (react-katex) | latest | LaTeX math rendering |
| cmdk | v1 | Command palette (search UI) |
| Fuse.js | v7 | Client-side fuzzy search |
| Tailwind CSS | v4 | Styling |
| specta | — | Rust-to-TypeScript type generation |

---

## Routes

```
apps/web/app/routes/
├── __root.tsx              # Root layout (topbar, providers)
├── index.tsx               # Landing: search + live feed + featured theorems
├── explore/
│   └── $theoremId.tsx      # Full-screen canvas explorer (React Flow)
├── domains/
│   ├── index.tsx           # Domain overview grid
│   └── $domain.tsx         # Theorems in a specific domain
├── axioms.tsx              # Browse seed axioms grouped by domain
├── timeline.tsx            # Chronological discovery feed
├── engine.tsx              # Technical: live stats, generation info, worker dashboard
├── auth/
│   ├── login.tsx           # Login form
│   ├── register.tsx        # Registration form
│   └── logout.tsx          # Logout action route
├── saved.tsx               # User's saved searches (auth required)
└── settings.tsx            # User preferences (auth required)
```

**Navigation bar (public):**
```
[Nasrudin]   Search | Domains | Axioms | Timeline | Engine     [Login]
```

Minimal top-level nav. Search is the default/home. Engine replaces the old
dashboard and worker page — it's where technical users go to see stats,
generation counts, worker activity, and system health.

---

## Key Pages

### 1. Landing Page (`/`) — Search + Discover

The homepage is a search interface with a live discovery feed. A visitor
immediately sees what Nasrudin is (a theorem search engine) and can use it.

```
┌──────────────────────────────────────────────────────────────────┐
│  Nasrudin     Domains   Axioms   Timeline   Engine       Login  │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│              Search formally verified physics theorems           │
│              847,231 theorems derived from first principles      │
│                                                                  │
│        ┌──────────────────────────────────────────────┐          │
│        │  E = mc^2                              [⌘K]  │          │
│        │  ┌──────────────────────────────────────┐    │          │
│        │  │  𝐸 = 𝑚𝑐²       (live KaTeX preview) │    │          │
│        │  └──────────────────────────────────────┘    │          │
│        ├──────────────────────────────────────────────┤          │
│        │  ● E² = (pc)² + (mc²)²    [SR]   d:8   →   │          │
│        │  ● E = ½mv²               [Mech] d:3   →   │          │
│        │  ● E = hν                  [QM]   d:2   →   │          │
│        │  ● ΔE = q + w             [Thermo] d:4  →   │          │
│        └──────────────────────────────────────────────┘          │
│                                                                  │
│  ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─  │
│                                                                  │
│  Live Discoveries                     Browse by Domain           │
│  ┌──────────────────────────┐  ┌────────────────────────────┐   │
│  │ ⚡ ∇×B = μ₀J + μ₀ε₀∂E/∂t│  │  Mechanics ········ 142K  │   │
│  │   [EM] depth:12  just now│  │  Electromagnetism ·· 98K   │   │
│  │                          │  │  Quantum Mechanics · 87K   │   │
│  │ ⚡ p = γmv               │  │  Special Relativity  64K   │   │
│  │   [SR] depth:5   2s ago  │  │  Thermodynamics ···  51K   │   │
│  │                          │  │  General Relativity  12K   │   │
│  │ ⚡ ∂ρ/∂t + ∇·J = 0      │  │                            │   │
│  │   [EM] depth:9   4s ago  │  │  [View all domains →]      │   │
│  └──────────────────────────┘  └────────────────────────────┘   │
│                                                                  │
│  Featured Theorems                                               │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐           │
│  │ E=mc²    │ │ F=ma     │ │ Maxwell  │ │ Schrödinger│          │
│  │ [Explore │ │ [Explore │ │ [Explore │ │ [Explore  │          │
│  │  graph →]│ │  graph →]│ │  graph →]│ │  graph →] │          │
│  └──────────┘ └──────────┘ └──────────┘ └──────────┘           │
└──────────────────────────────────────────────────────────────────┘
```

**Sections (top to bottom):**

1. **Hero search bar** — centered, prominent. Subtitle shows total theorem
   count (SSE-updated). Typing opens the command palette inline with live
   KaTeX preview and results. Each result has a `→` that navigates directly
   to `/explore/:theoremId`.

2. **Live discovery feed** — SSE-driven ticker of theorems being verified
   right now. Shows the system is alive. Each entry is clickable → explore.

3. **Browse by domain** — quick links to the six physics domains with theorem
   counts. One click to filtered browsing.

4. **Featured theorems** — curated cards for famous results (energy-mass
   equivalence, Newton's laws, Maxwell's equations). Each links to its full
   derivation graph. This gives newcomers an obvious starting point.

**Data sources:**
- Search: Fuse.js client-side (top 10K cached) + server `GET /api/search?q=...`
- Live feed: SSE `/api/events/discoveries`
- Domain counts: `GET /api/stats` (polled every 30s)
- Featured: hardcoded theorem IDs, fetched via `GET /api/theorems/:id`
- Total count: SSE `/api/events/stats`

### 2. Canvas Explorer (`/explore/:theoremId`)

Full-screen interactive derivation graph. This is the core experience after
search. The user clicks a theorem and sees exactly how it was derived from
axioms, with every step formally verified.

```
┌──────────────────────────────────────────────────────────────────┐
│  ← Back to search    E² = (pc)² + (mc²)²    [SR] depth:8      │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────────────────────────────┐  ┌───────────┐ │
│  │                                             │  │  Detail   │ │
│  │        [F = ma]  ──────┐                    │  │  Panel    │ │
│  │                        ▼                    │  │           │ │
│  │  [E = ½mv²]  ──→ [Work-Energy] ──┐         │  │  Formula: │ │
│  │                                   ▼         │  │  E²=(pc)² │ │
│  │  [p = mv]  ───────────────→ [E-p relation]  │  │  +(mc²)²  │ │
│  │                                   │         │  │           │ │
│  │  [c = const] ──→ [γ factor] ──────┘         │  │  Domain:  │ │
│  │                                             │  │  SR       │ │
│  │                                             │  │           │ │
│  │                    [Minimap]                 │  │  Depth: 8 │ │
│  │                    ┌─────┐                  │  │  Gen: 5018│ │
│  │                    │ ·   │                  │  │           │ │
│  │                    └─────┘                  │  │  Parents:3│ │
│  └─────────────────────────────────────────────┘  │  Children:│ │
│                                                    │  12       │ │
│  Domain: ☑Mech ☑SR ☑EM ☐QM    Depth: [0──●──20]  │           │ │
│                                                    │ [Copy TeX]│ │
│                                                    │ [Save]    │ │
│                                                    └───────────┘ │
└──────────────────────────────────────────────────────────────────┘
```

**Layout:**
- Graph canvas takes ~75% width. Detail panel ~25% on the right.
- Filter bar pinned at the bottom of the canvas area.
- Back link returns to search (or wherever the user came from).

**Initial load:**
1. Fetch theorem + lineage: `GET /api/theorems/:id/lineage`
2. Layout with dagre (hierarchical, top-to-bottom)
3. Render with React Flow

**Interactions:**
- **Click node** → populate detail panel (full proof, metadata, fitness)
- **Double-click node** → expand its parents and children (WebSocket `expand`)
- **Right-click node** → context menu: copy LaTeX, open in new tab, view in search
- **Scroll** → zoom in/out
- **Drag** → pan canvas
- **Minimap** → overview navigation (bottom-right of canvas)
- **Filters** → domain toggles, depth range slider, complexity slider

**Detail panel tabs:**

The right-side detail panel has three tabs when a node is selected:

| Tab | Contents |
|-----|----------|
| **Overview** | KaTeX formula, domain badge, depth, generation, fitness scores, parent/child counts |
| **Proof** | Tactic script (syntax-highlighted), proof tree visualization, verification metadata (timestamp, tactic, duration, Lean4 version), "Download .lean" button, "Copy proof term" button |
| **Lineage** | List of parent theorems (clickable), list of child theorems (clickable), axiom ancestors (transitive roots) |

The **Proof tab** is the primary interface for academic validation. It shows
exactly how the theorem was verified and provides a one-click `.lean` export.

**Node types:**
```
┌─────────────────────┐     ┌─────────────────────┐
│  AXIOM NODE         │     │  THEOREM NODE        │
│  ─────────          │     │  ────────────        │
│  ┌───────────────┐  │     │  ┌───────────────┐   │
│  │  F = ma       │  │     │  │ E² = p²c² +   │   │
│  │  (KaTeX)      │  │     │  │ (mc²)²        │   │
│  └───────────────┘  │     │  └───────────────┘   │
│  [Mechanics] d:0    │     │  [SR] d:8  g:5018   │
│  ● Axiom            │     │  ▲ 3 parents         │
└─────────────────────┘     │  ▼ 12 children       │
  gold border               └─────────────────────┘
                              domain-colored border
```

**Edge types:**
- Solid arrow: direct derivation (parent → child)
- Dashed arrow: simplification step
- Thick arrow: multiple inference steps collapsed

**Layout algorithm:**
- dagre for hierarchical layout (axioms at top, derived flowing down)
- Group by domain with subtle background coloring
- Future: force-directed option for seeing clusters

### 3. Domain Browser (`/domains` and `/domains/:domain`)

**Overview page (`/domains`):** grid of domain cards showing name, theorem
count, a sample formula, and recent discovery rate.

**Domain detail (`/domains/:domain`):**
- Theorems grouped by depth (axioms first, then depth 1, 2, ...)
- Each card: KaTeX formula + depth + fitness + child count
- Click any card → `/explore/:theoremId`
- Sort options: depth, fitness, recency, child count

### 4. Axioms Page (`/axioms`)

Browse the seed axioms that everything derives from. Grouped by domain.
Each axiom card shows: formula, domain, child count (how many theorems
descend from it). Click → explore its descendants in the graph.

### 5. Timeline (`/timeline`)

Chronological stream of discoveries.

- Infinite scroll list
- Each entry: timestamp, formula (KaTeX), domain, depth
- Filter by domain, minimum fitness, date range
- SSE for real-time new entries at the top
- Click any entry → `/explore/:theoremId`

### 6. Engine Page (`/engine`)

Technical dashboard for people who want to see how the system works.
**This is NOT the landing page.** It's opt-in for curious/technical users.

```
┌──────────────────────────────────────────────────────────────────┐
│  Engine Status                                                   │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────┐ ┌──────┐ ┌──────────┐ ┌──────────┐ ┌──────────────┐  │
│  │ 847K │ │ 142/s│ │ Gen 5021 │ │ 94.2%    │ │ 8 workers    │  │
│  │total │ │ rate │ │generation│ │ verified │ │ active       │  │
│  └──────┘ └──────┘ └──────────┘ └──────────┘ └──────────────┘  │
│                                                                  │
│  Discovery Rate (24h)            Domain Distribution             │
│  ┌───────────────────────┐  ┌────────────────────────────────┐  │
│  │  ╱╲    ╱╲             │  │   ██████████ Mechanics  142K   │  │
│  │ ╱  ╲╱╱  ╲    ╱╲      │  │   ████████  EM         98K    │  │
│  │╱         ╲╱╱  ╲╱     │  │   ███████   QM         87K    │  │
│  └───────────────────────┘  │   █████     SR         64K    │  │
│                              └────────────────────────────────┘  │
│                                                                  │
│  Active Workers                                                  │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │  Name          Status    Theorems    Gen     Uptime      │   │
│  │  worker-alpha  online    12,481      3201    4d 12h      │   │
│  │  worker-beta   online     8,293      2814    2d 6h       │   │
│  │  worker-gamma  offline    5,102      1920    —           │   │
│  └──────────────────────────────────────────────────────────┘   │
│                                                                  │
│  How It Works                                                    │
│  Genetic algorithm → pre-filter → Lean4 formal verification     │
│  [Read the architecture docs →]                                  │
└──────────────────────────────────────────────────────────────────┘
```

**Sections:**
- Stats grid (SSE-updated): total theorems, rate, generation, verification %, active workers
- Discovery rate sparkline (24h chart)
- Domain distribution bar chart
- Worker table: name, status, contribution count, generation, uptime
- Brief "How It Works" blurb with link to full architecture docs

**Data sources:**
- Stats: SSE `/api/events/stats`
- Workers: `GET /api/workers` (polled every 10s)
- Domain chart: `GET /api/stats`

---

## Component Architecture

```
App
├── Layout
│   ├── TopBar (logo, nav links, search shortcut ⌘K, auth menu)
│   └── (no sidebar — full-width pages)
├── Routes
│   ├── LandingPage (/)
│   │   ├── HeroSearch
│   │   │   ├── SearchBar (cmdk-powered, inline results)
│   │   │   │   ├── LatexInput (contenteditable + KaTeX preview)
│   │   │   │   ├── ClientResults (Fuse.js)
│   │   │   │   └── ServerResults (TanStack Query)
│   │   │   └── TheoremCount (SSE-updated total)
│   │   ├── LiveDiscoveryTicker (SSE stream, latest 10)
│   │   ├── DomainQuickLinks (6 domain cards with counts)
│   │   └── FeaturedTheorems (curated cards → explore)
│   ├── ExplorePage (/explore/:theoremId)
│   │   ├── ExploreHeader (back link, theorem title, domain badge)
│   │   ├── GraphCanvas (React Flow)
│   │   │   ├── AxiomNode (gold border, KaTeX, domain)
│   │   │   ├── TheoremNode (domain-colored, KaTeX, stats)
│   │   │   ├── DerivationEdge (solid/dashed/thick)
│   │   │   └── MiniMap
│   │   ├── DetailPanel (right sidebar, tabbed)
│   │   │   ├── OverviewTab (formula, domain, depth, fitness)
│   │   │   ├── ProofTab (tactic script, proof tree, download .lean)
│   │   │   │   ├── TacticDisplay (syntax-highlighted Lean4 tactic)
│   │   │   │   ├── ProofTreeView (collapsible step-by-step derivation)
│   │   │   │   ├── VerificationMeta (timestamp, tactic, duration, Lean4 version)
│   │   │   │   ├── DownloadLeanButton (GET /api/theorems/:id/proof.lean)
│   │   │   │   └── CopyProofTermButton (raw proof term to clipboard)
│   │   │   └── LineageTab (parent list, child list, axiom ancestors)
│   │   └── FilterBar (domain toggles, depth slider)
│   ├── DomainsPage (/domains)
│   │   └── DomainCard[] (name, count, sample formula, rate)
│   ├── DomainDetailPage (/domains/:domain)
│   │   └── TheoremGrid (grouped by depth, sortable)
│   ├── AxiomsPage (/axioms)
│   │   └── AxiomList (grouped by domain, each shows child count)
│   ├── TimelinePage (/timeline)
│   │   └── DiscoveryList (infinite scroll, SSE for new entries)
│   ├── EnginePage (/engine)
│   │   ├── StatsGrid (total, rate, generation, verified %)
│   │   ├── RateChart (24h sparkline)
│   │   ├── DomainDistribution (bar chart)
│   │   └── WorkerTable (name, status, contributions)
│   ├── AuthPages (/auth/*)
│   │   ├── LoginPage
│   │   └── RegisterPage
│   ├── SavedPage (/saved — auth required)
│   └── SettingsPage (/settings — auth required)
├── Shared Components
│   ├── TheoremCard (KaTeX formula, domain badge, depth, → explore link)
│   ├── DomainBadge (colored pill: Mechanics, EM, QM, SR, Thermo, GR)
│   ├── KaTeXBlock (rendered formula)
│   ├── SearchBar (reusable, appears in TopBar as ⌘K trigger too)
│   └── LiveDot (pulsing indicator for SSE-connected elements)
├── Auth
│   ├── AuthGuard (redirect if not authenticated)
│   └── UserMenu (avatar dropdown: saved, settings, logout)
└── Providers
    ├── QueryClientProvider (TanStack Query)
    ├── AuthProvider (session token, current user state)
    ├── SSEProvider (discovery + stats streams)
    └── ThemeProvider
```

---

## User Flows

### Flow 1: Search → Explore (primary)

```
Landing page → type in search bar → see results with KaTeX preview
  → click result → /explore/:theoremId → full derivation graph
  → click nodes to see details → double-click to expand → explore lineage
```

This is the core loop. It should feel as fast as using a search engine.

### Flow 2: Browse → Explore

```
Landing page → click domain card → /domains/:domain → browse theorems
  → click theorem → /explore/:theoremId → graph
```

Or:
```
Landing page → click featured theorem → /explore/:theoremId → graph
```

### Flow 3: Watch Discoveries

```
Landing page → watch live ticker → click an interesting discovery
  → /explore/:theoremId → see how it was just derived
```

Or for deeper browsing:
```
Nav → Timeline → scroll through history → click entry → explore
```

### Flow 4: Technical Deep-Dive

```
Nav → Engine → see stats, workers, generation info → understand the system
```

### Flow 5: Academic Proof Validation

```
Search/browse → find theorem → /explore/:theoremId → click node
  → Detail panel "Proof" tab → view tactic script + proof tree
  → click "Download .lean" → save standalone Lean4 file
  → run `lake build` locally → independent re-verification
```

This flow requires no login. All proofs are publicly accessible. The
downloaded `.lean` file is self-contained — it imports the Nasrudin axiom
definitions and includes the full proof term, so `lake build` can verify
it from scratch without trusting the server.

---

## Real-Time Data

### SSE Subscriptions

```typescript
// lib/sse.ts
import { useEffect } from 'react';
import { useQueryClient } from '@tanstack/react-query';

export function useDiscoveryStream() {
  const queryClient = useQueryClient();

  useEffect(() => {
    const es = new EventSource('/api/events/discoveries');

    es.addEventListener('new_theorem', (event) => {
      const theorem = JSON.parse(event.data);
      // Update cache
      queryClient.setQueryData(['theorem', theorem.id], theorem);
      // Invalidate list queries
      queryClient.invalidateQueries({ queryKey: ['theorems'] });
    });

    es.addEventListener('stats_update', (event) => {
      const stats = JSON.parse(event.data);
      queryClient.setQueryData(['stats'], (old) => ({ ...old, ...stats }));
    });

    es.addEventListener('milestone', (event) => {
      // Show toast for milestones (100K, 500K, 1M theorems, etc.)
      const { message } = JSON.parse(event.data);
      toast.success(message);
    });

    return () => es.close();
  }, [queryClient]);
}
```

### WebSocket for Graph Exploration

```typescript
// lib/ws.ts
export function useGraphExplorer(theoremId: string) {
  const ws = useRef<WebSocket | null>(null);
  const [graphData, setGraphData] = useState<GraphResponse>();

  useEffect(() => {
    ws.current = new WebSocket(`/api/ws/explore`);

    ws.current.onopen = () => {
      // Request initial graph for theorem
      ws.current?.send(JSON.stringify({
        type: 'load',
        theoremId,
        depth: 2, // Load 2 levels of parents/children
      }));
    };

    ws.current.onmessage = (event) => {
      const msg = JSON.parse(event.data);
      switch (msg.type) {
        case 'graph_update':
          setGraphData(msg.data);
          break;
        case 'node_expanded':
          // Merge new nodes/edges into existing graph
          setGraphData(prev => mergeGraph(prev, msg.data));
          break;
      }
    };

    return () => ws.current?.close();
  }, [theoremId]);

  const expandNode = (nodeId: string) => {
    ws.current?.send(JSON.stringify({
      type: 'expand',
      theoremId: nodeId,
    }));
  };

  return { graphData, expandNode };
}
```

---

## Type Safety (Rust → TypeScript)

Using `specta` crate to generate TypeScript interfaces from Rust structs:

```rust
// engine/crates/api/src/types.rs
use specta::Type;
use serde::Serialize;

#[derive(Serialize, Type)]
pub struct TheoremResponse {
    pub id: String,
    pub latex: String,
    pub domain: Domain,
    pub depth: u32,
    pub complexity: u32,
    pub fitness: FitnessScore,
    pub verified: bool,
    pub generation: u64,
    pub created_at: u64,
    pub parent_ids: Vec<String>,
    pub child_count: u32,
}
```

Build step generates `packages/shared-types/src/index.ts`:
```typescript
// Auto-generated by specta — DO NOT EDIT
export interface TheoremResponse {
  id: string;
  latex: string;
  domain: Domain;
  depth: number;
  complexity: number;
  fitness: FitnessScore;
  verified: boolean;
  generation: number;
  created_at: number;
  parent_ids: string[];
  child_count: number;
}
```

---

## Authentication Flow

Auth uses session tokens stored in HTTP-only cookies. PostgreSQL stores the
user and session records; the Axum API handles bcrypt hashing and token
generation.

```
Register/Login → POST /api/auth/register or /api/auth/login
                → Axum validates, creates session in PostgreSQL
                → Returns Set-Cookie (httpOnly, secure, sameSite)
                → Frontend AuthProvider reads user from /api/auth/me
                → Subsequent requests include cookie automatically
```

Protected routes (`/saved`, `/settings`) use an `AuthGuard` wrapper that
redirects to `/auth/login` if no valid session exists. All other routes are
fully public — no authentication needed to search, explore, or browse.

**Data sources by database:**

| Frontend Feature | Database | Endpoint |
|-----------------|----------|----------|
| Theorem search, explore, lineage | RocksDB | `/api/theorems/*`, `/api/search` |
| Proof viewer, proof export | RocksDB | `/api/theorems/:id/proof`, `/api/theorems/:id/proof.lean` |
| Live stats, SSE streams | RocksDB | `/api/stats`, `/api/events/*` |
| Login, register, session | PostgreSQL | `/api/auth/*` |
| Saved searches | PostgreSQL | `/api/saved-searches` |
| User preferences | PostgreSQL | `/api/preferences` |
| Worker dashboard | PostgreSQL | `/api/workers` |

---

## Visual Design

### Light Theme

The default (and only) theme is **light**. White/near-white backgrounds with
dark text, modeled after academic papers and scientific journals. This
reinforces that the content is formally verified mathematics — it should
feel like reading a well-typeset paper, not a hacker dashboard.

**Palette:**

| Token | Value | Usage |
|-------|-------|-------|
| `--bg` | `#FFFFFF` | Page background |
| `--bg-subtle` | `#F8FAFC` | Card backgrounds, panels |
| `--bg-muted` | `#F1F5F9` | Hover states, graph canvas background |
| `--border` | `#E2E8F0` | Card borders, dividers |
| `--text` | `#0F172A` | Primary text (slate-900) |
| `--text-secondary` | `#475569` | Metadata, labels (slate-600) |
| `--text-muted` | `#94A3B8` | Timestamps, subtle info (slate-400) |
| `--accent` | `#1E40AF` | Links, active states (blue-800) |

The graph canvas uses `--bg-muted` so nodes (white cards) pop against a
slightly tinted background. The detail panel and cards use `--bg-subtle`
for gentle separation without heavy borders.

### Domain Colors

Each physics domain has a consistent color used in badges, node borders,
and chart segments. These are chosen to be distinguishable on a light
background and readable as badge text on white cards:

| Domain | Color | Hex | Badge BG |
|--------|-------|-----|----------|
| Mechanics | Blue | `#2563EB` | `#DBEAFE` |
| Electromagnetism | Amber | `#D97706` | `#FEF3C7` |
| Quantum Mechanics | Violet | `#7C3AED` | `#EDE9FE` |
| Special Relativity | Red | `#DC2626` | `#FEE2E2` |
| Thermodynamics | Emerald | `#059669` | `#D1FAE5` |
| General Relativity | Rose | `#E11D48` | `#FFE4E6` |

Badges use the light `Badge BG` with the saturated `Hex` as text color.
Node borders in the graph use the saturated `Hex`. Chart segments use the
saturated color at 80% opacity.

### Typography

- **UI text**: Inter (or system sans-serif fallback). Clean, modern, high
  x-height for readability at small sizes.
- **Formulas**: KaTeX renders in Computer Modern — the same font used in
  LaTeX documents. This is intentional: formulas should look like they
  belong in a paper.
- **Monospace**: JetBrains Mono or system monospace. Used sparingly for
  theorem IDs and technical metadata.
- **Headings**: Inter at medium/semibold weight. No all-caps, no decorative fonts.

The visual contrast between Inter (UI) and Computer Modern (math) creates
a natural distinction between chrome and content.

### Key Visual Elements

- **Axiom nodes**: gold/amber left border accent (`#D97706`), distinct from derived theorems
- **Theorem nodes**: white cards with domain-colored left border
- **Live indicators**: subtle pulsing green dot next to SSE-connected elements
- **Verified badge**: small checkmark icon on every theorem (they're all formally verified)
- **Depth indicator**: subtle number or thin bar showing derivation distance from axioms
- **Shadows**: minimal, low-opacity. Cards use `shadow-sm`. No heavy drop shadows.
- **Borders**: `1px solid var(--border)` on cards. Clean lines, no rounded-to-pill shapes.
  Modest border-radius (`6-8px`) on cards and badges.

The overall feel: **clean, spacious, typographic** — closer to a research
paper viewer than a SaaS dashboard.

---

## Performance Considerations

| Concern | Solution |
|---------|----------|
| Large graph rendering | React Flow virtualizes — only renders visible nodes |
| KaTeX rendering many formulas | Pre-render to HTML strings on server, hydrate on client |
| Formula index size (10K+) | Fuse.js handles 100K items easily; paginate server results |
| SSE reconnection | EventSource auto-reconnects; TanStack Query handles stale data |
| WebSocket graph data | Send incremental diffs, not full graphs |
| Initial page load | TanStack Start SSR streams HTML immediately |
| Search responsiveness | Client-side Fuse.js for instant results, server for full coverage |
| Landing page load | Featured theorems SSR'd, search bar interactive immediately |
