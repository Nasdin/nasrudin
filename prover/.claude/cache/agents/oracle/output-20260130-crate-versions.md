# Research Report: Latest Rust Crate Versions (January 2026)
Generated: 2026-01-30

## Summary

All 19 requested crates have been researched with their latest stable versions as of January 2026. SeaORM 2.x is NOT yet stable -- it is at release candidate 2.0.0-rc.28; the latest stable is 1.1.19. The latest Rust edition is 2024 (shipped with Rust 1.85.0), the latest stable Rust compiler is 1.93.0, and the latest Lean4 stable is v4.27.0.

## Crate Version Table

| # | Crate | Latest Stable | Notes |
|---|-------|---------------|-------|
| 1 | `axum` | **0.8.8** | Web framework by tokio-rs |
| 2 | `rocksdb` | **0.24.0** | Rust bindings (released 2025-08-10) |
| 3 | `sea-orm` | **1.1.19** (stable) / **2.0.0-rc.28** (pre-release) | See SeaORM section below |
| 4 | `sqlx` | **0.8.6** | Async SQL toolkit; 0.9.0-alpha.1 pre-release exists |
| 5 | `serde` | **1.0.228** | Released 2025-09-27 |
| 6 | `serde_json` | **1.0.145** | Released 2025-09-14 |
| 7 | `tokio` | **1.49.0** | Released ~2026-01-08; LTS: 1.43.x and 1.47.x |
| 8 | `anyhow` | **1.0.100** | Flexible error type |
| 9 | `thiserror` | **2.0.18** | Released 2026-01-18 (major version 2.x!) |
| 10 | `tracing` | **0.1.41** | Application-level tracing |
| 11 | `tracing-subscriber` | **0.3.20** | Subscriber implementations |
| 12 | `xxhash-rust` | **0.8.15** | xxHash implementation |
| 13 | `prost` | **0.14.2** | Protobuf; released 2025-12-01 |
| 14 | `bytes` | **1.11.0** | Released 2025-11-14 |
| 15 | `hex` | **0.4.3** | Hex encoding/decoding |
| 16 | `tower-http` | **0.6.6** | HTTP-specific Tower utilities |
| 17 | `uuid` | **1.18.1** | UUID generation and parsing |
| 18 | `chrono` | **0.4.42** | Date and time library |
| 19 | `rand` | **0.9.2** | Random number generation; 0.10.0-rc.6 pre-release exists |

## Cargo.toml Snippet

```toml
[dependencies]
axum = "0.8"
rocksdb = "0.24"
sea-orm = "1.1"                          # or "2.0.0-rc.28" for pre-release
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tokio = { version = "1.49", features = ["full"] }
anyhow = "1.0"
thiserror = "2.0"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
xxhash-rust = { version = "0.8", features = ["xxh3"] }
prost = "0.14"
bytes = "1.11"
hex = "0.4"
tower-http = { version = "0.6", features = ["cors", "trace"] }
uuid = { version = "1.18", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
rand = "0.9"
```

## SeaORM 2.x Status

**Answer: SeaORM 2.0 is NOT yet stable.** It is in release candidate phase.

- **Latest stable:** 1.1.19
- **Latest pre-release:** 2.0.0-rc.28 (published 2026-01-11)
- RC series began 2025-07-05 with rc.1 and has gone through 28 release candidates
- The SeaORM team committed to maintaining 1.x until at least October 2025, after which they would decide on 2.0

**Recommendation:** If you want to use SeaORM 2.x, you can pin to `2.0.0-rc.28` but expect breaking changes between RCs. For production stability, use `1.1.19`. Given 28 RCs, a stable 2.0.0 release seems likely in early-to-mid 2026.

## SQLx vs SeaORM

SQLx and SeaORM serve different purposes and are complementary:

- **SQLx** is a raw async SQL toolkit with compile-time checked queries. It is NOT an ORM.
- **SeaORM** is a full ORM built on top of SeaQuery. It can use SQLx as its underlying database driver.
- They do NOT replace each other. If using SeaORM, you typically do NOT also need a direct SQLx dependency (SeaORM handles the driver internally via features like `sea-orm = { features = ["sqlx-postgres"] }`).
- If you prefer raw SQL with compile-time safety, use SQLx directly. If you want an ORM, use SeaORM.

## Rust Toolchain

| Item | Version |
|------|---------|
| **Latest Rust Edition** | **2024** (stabilized in Rust 1.85.0, February 20, 2025) |
| **Latest Stable Rust** | **1.93.0** (released January 22, 2026) |
| **Beta** | 1.94.0 (expected March 5, 2026) |

Key 2024 edition features: async closures, `#[diagnostic::do_not_recommend]`, `unsafe` required for `std::env::set_var`, `Future`/`IntoFuture` in prelude.

## Lean4

| Item | Version |
|------|---------|
| **Latest Lean4 Stable** | **v4.27.0** (released January 23, 2026) |
| **Latest RC** | v4.28.0-rc1 (January 26, 2026) |

Lean4 releases monthly, with the stable release at month-end being identical to the last RC.

## Notable Version Surprises

1. **thiserror jumped to 2.x** -- The latest is 2.0.18, not 1.x. This is a major version bump; check migration notes if upgrading from 1.x.
2. **rand is now 0.9.x** -- Major API changes from 0.8.x. A 0.10.0 is in RC.
3. **prost jumped to 0.14.x** -- Up from 0.13.x, with protocol buffers improvements.
4. **tokio remains on 1.x** -- No tokio 2.0 on the horizon. LTS releases available.

## Sources

1. [axum on crates.io](https://crates.io/crates/axum)
2. [axum 0.8.8 on docs.rs](https://docs.rs/crate/axum/latest)
3. [rocksdb on crates.io](https://crates.io/crates/rocksdb)
4. [rocksdb 0.24.0 on docs.rs](https://docs.rs/crate/rocksdb/latest)
5. [sea-orm on crates.io](https://crates.io/crates/sea-orm)
6. [sea-orm 1.1.19 on docs.rs](https://docs.rs/crate/sea-orm/latest)
7. [sea-orm 2.0.0-rc.7 on crates.io](https://crates.io/crates/sea-orm/2.0.0-rc.7)
8. [sqlx on crates.io](https://crates.io/crates/sqlx)
9. [sqlx 0.8.6 on docs.rs](https://docs.rs/crate/sqlx/latest)
10. [serde 1.0.228 on docs.rs](https://docs.rs/crate/serde/latest)
11. [serde_json 1.0.145 on docs.rs](https://docs.rs/crate/serde_json/latest)
12. [tokio on crates.io](https://crates.io/crates/tokio)
13. [tokio 1.49.0 on docs.rs](https://docs.rs/crate/tokio/latest/source/README.md)
14. [anyhow on crates.io](https://crates.io/crates/anyhow)
15. [anyhow 1.0.100 on docs.rs](https://docs.rs/crate/anyhow/latest)
16. [thiserror 2.0.18 on docs.rs](https://docs.rs/crate/thiserror/latest)
17. [tracing 0.1.41 on docs.rs](https://docs.rs/crate/tracing/latest)
18. [tracing-subscriber on crates.io](https://crates.io/crates/tracing-subscriber)
19. [xxhash-rust 0.8.15 on docs.rs](https://docs.rs/crate/xxhash-rust/latest)
20. [prost on crates.io](https://crates.io/crates/prost)
21. [bytes 1.11.0 on docs.rs](https://docs.rs/crate/bytes/latest)
22. [hex on crates.io](https://crates.io/crates/hex)
23. [tower-http 0.6.6 on docs.rs](https://docs.rs/crate/tower-http/latest)
24. [uuid on crates.io](https://crates.io/crates/uuid)
25. [chrono on crates.io](https://crates.io/crates/chrono)
26. [rand 0.9.2 on docs.rs](https://docs.rs/crate/rand/latest)
27. [Announcing Rust 1.93.0](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/)
28. [Announcing Rust 1.85.0 and Rust 2024](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/)
29. [Lean4 Releases](https://github.com/leanprover/lean4/releases)
30. [Rust 2024 Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)
