# Engine Workspace Crates

```
engine/crates/
├── core/         — Shared types: Expr AST, Theorem, ProofTree, FitnessScore, Domain, Dimension
├── rocks/        — RocksDB storage: 9 column families, CRUD + indexes + stats
├── derive/       — Algebraic derivation: rewrite engine, axiom store, strategies, dimension checker
├── ga/           — Genetic algorithms: crossover, mutation, selection, fitness, island model
├── lean-bridge/  — Lean4 communication: process-based verification, export pipeline
├── api/          — Axum daemon: HTTP API + SSE + GA thread + verification workers
│   src/admin/          — RequireAdmin extractor, perform_audited, action taxonomy, bulk runner, expiry tick
│   src/billing/refund* — DB-first → Stripe refund flow + 60s reconciler
│   src/trust.rs        — Trust resolution + cache + 1-in-N spot-check sampling
│   src/impersonation.rs — HMAC token mint/verify + middleware
│   src/handlers/admin/ — admin HTTP handlers (users, keys, jobs, audit_log, stats, bulk, ...)
├── pg/           — PostgreSQL via SeaORM: users, sessions, workers, billing, library, conjectures
├── mcp/          — [STUB] MCP protocol server for LLM-assisted curation
└── importer/     — Theorem importer from Mathlib/PhysLean (Lean→Expr translator)