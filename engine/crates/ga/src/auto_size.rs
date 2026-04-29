//! Resource-budget auto-detection for the GA worker (P-Task 6).
//!
//! The platform supports two deployment shapes:
//!
//! 1. **Central server** — single big-box DO droplet (target 64 CPU /
//!    250 GB RAM). Runs the API, Postgres, RocksDB, and the lake-build
//!    pool. The API's `LakeBuilder` reads a budget from this module
//!    too.
//! 2. **Distributed workers** — thousands of school-volunteer machines
//!    of every shape (4-core laptop to 32-core lab box). Each worker
//!    auto-sizes its GA population, lake-slot count, and chunking
//!    schedule to its hardware so users don't have to tune flags.
//!
//! Detection sources:
//!
//! - `std::thread::available_parallelism()` for logical cores. Honors
//!   container cpu limits via cgroups on Linux + Docker. Falls back to
//!   `num_cpus::get_physical()` if the std API is unavailable.
//! - `sysinfo::System::total_memory()` for RAM. Honors cgroup memory
//!   limits inside Docker.
//! - `NASRUDIN_RESERVE_CORES` env var (default 2) for cores held back
//!   for OS / API / Postgres so the worker never starves the box.
//! - `NASRUDIN_RESERVE_RAM_GB` env var (default 8) — same for RAM.
//!
//! A `lean` worker process holds ~1.5–2 GB resident, so the RAM
//! budget per lake slot is calibrated to 2.5 GB to leave headroom for
//! short-lived GC spikes during proof elaboration.

use std::time::Duration;

/// Resource budget the worker (and the central server's `LakeBuilder`)
/// uses to scale its parallelism + GA size to the host.
#[derive(Debug, Clone)]
pub struct ResourceBudget {
    /// Logical cores available to the process (cgroup-aware).
    pub cores: usize,
    /// Total RAM available, in MiB (cgroup-aware).
    pub ram_mib: u64,
    /// How many parallel `lake build` invocations can safely run
    /// without OOM. Bounded by `min(cores - reserve, ram_mib / 2_500)`.
    pub lake_slots: usize,
    /// GA population size. `lake_slots × 4` so each lake slot has
    /// fresh candidates queued up. Floor 32.
    pub pop_size: usize,
    /// GA generations. High by default — workers are expected to
    /// grind for hours/days.
    pub gens: usize,
    /// Number of chunks the GA execution is sliced into. Each chunk
    /// boundary triggers seed-sync + status reporting. `lake_slots × 2`
    /// so each chunk does meaningful work; floor 8.
    pub chunks: usize,
    /// Per-chunk lake-verification budget. Independent of `lake_slots`
    /// (slots = concurrency, this = total).
    pub max_lake_per_chunk: usize,
    /// Safety: kill the worker if a single GA step takes longer than
    /// this. Detects pathological chains.
    pub step_timeout: Duration,
}

impl ResourceBudget {
    /// Detect the budget from the host. Honors env-var overrides:
    ///
    /// - `NASRUDIN_RESERVE_CORES` (default 2) — cores held back for OS+API
    /// - `NASRUDIN_RESERVE_RAM_GB` (default 8) — RAM held back
    /// - `NASRUDIN_LAKE_SLOTS_OVERRIDE` (default unset) — force lake slots
    /// - `NASRUDIN_POP_OVERRIDE` (default unset) — force pop_size
    /// - `NASRUDIN_GENS_OVERRIDE` (default unset) — force gens
    ///
    /// Logged via `tracing::info!` so operators can see what the
    /// worker decided.
    pub fn detect() -> Self {
        let reserve_cores: usize = std::env::var("NASRUDIN_RESERVE_CORES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(2);
        let reserve_ram_gb: u64 = std::env::var("NASRUDIN_RESERVE_RAM_GB")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8);

        let cores = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or_else(|_| num_cpus::get());

        let mut sys = sysinfo::System::new();
        sys.refresh_memory();
        // sysinfo returns bytes in newer versions; we want MiB.
        let ram_bytes = sys.total_memory();
        let ram_mib = ram_bytes / (1024 * 1024);
        let usable_ram_mib = ram_mib.saturating_sub(reserve_ram_gb * 1024);

        // lake_slots: bounded by both CPU and RAM. Each lake slot needs
        // ~2.5 GB at peak (Lean elaborator + Mathlib oleans + temp build
        // artifacts).
        let cpu_capped = cores.saturating_sub(reserve_cores).max(1);
        let ram_capped = (usable_ram_mib / 2500) as usize;
        let mut lake_slots = cpu_capped.min(ram_capped).max(1);
        if let Ok(o) = std::env::var("NASRUDIN_LAKE_SLOTS_OVERRIDE") {
            if let Ok(v) = o.parse::<usize>() {
                lake_slots = v.max(1);
            }
        }

        let mut pop_size = (lake_slots * 4).max(32);
        if let Ok(o) = std::env::var("NASRUDIN_POP_OVERRIDE") {
            if let Ok(v) = o.parse::<usize>() {
                pop_size = v.max(8);
            }
        }
        let mut gens = 5000;
        if let Ok(o) = std::env::var("NASRUDIN_GENS_OVERRIDE") {
            if let Ok(v) = o.parse::<usize>() {
                gens = v.max(1);
            }
        }
        let chunks = (lake_slots * 2).max(8);
        let max_lake_per_chunk = (lake_slots * 3).max(6);

        let budget = Self {
            cores,
            ram_mib,
            lake_slots,
            pop_size,
            gens,
            chunks,
            max_lake_per_chunk,
            step_timeout: Duration::from_secs(180),
        };

        tracing::info!(
            cores = cores,
            ram_mib = ram_mib,
            lake_slots = lake_slots,
            pop_size = pop_size,
            gens = gens,
            chunks = chunks,
            max_lake_per_chunk = max_lake_per_chunk,
            "ResourceBudget::detect"
        );
        eprintln!(
            "▶ ResourceBudget: {cores} cores, {ram_mib} MiB RAM → \
             lake_slots={lake_slots}, pop={pop_size}, gens={gens}, \
             chunks={chunks}, max_lake/chunk={max_lake_per_chunk}"
        );

        budget
    }
}
