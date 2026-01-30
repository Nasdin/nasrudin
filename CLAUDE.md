# Engine Workspace Crates

```
engine/crates/
├── core/         — Shared types: Expr AST, Theorem, ProofTree, FitnessScore, Domain, Dimension
├── rocks/        — RocksDB storage: 9 column families, CRUD + indexes + stats
├── derive/       — Algebraic derivation: rewrite engine, axiom store, strategies, dimension checker
├── ga/           — Genetic algorithms: crossover, mutation, selection, fitness, island model
├── lean-bridge/  — Lean4 communication: process-based verification, export pipeline
├── api/          — Axum daemon: HTTP API + SSE + GA thread + verification workers
├── pg/           — [STUB] PostgreSQL via SeaORM: users, sessions, worker tracking
├── mcp/          — [STUB] MCP protocol server for LLM-assisted curation
└── importer/     — [STUB] Theorem importer from Mathlib/PhysLean