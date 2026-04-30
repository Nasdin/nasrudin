# Worker Release + Landing-page De-mock — Design

**Date:** 2026-04-30
**Status:** Approved (pending spec review)
**Goal:** Cut the first public worker binary release (`worker-v0.1.0`) on `github.com/Nasdin/nasrudin`, and make the landing page truthfully describe what a user sees when they download and run it. Replace every mocked CLI / log fixture / event ticker on the landing with output captured from the actual worker binary or from the live API.

---

## 1. Scope

Three deliverables, end-to-end:

1. **Local cross-compile build pipeline** for the discovery worker, replacing `.github/workflows/release-worker.yml` with a `just` recipe that builds five platform bundles on this Mac and uploads them to a GitHub release via `gh`.
2. **Public-readiness chores** for the repo: add an AGPL-3.0 `LICENSE`, fix a README typo, ensure the first release tag lands on a clean tree.
3. **Landing-page de-mock**: replace `InstallNode` with a real download-and-run UX; replace `GAViz`'s hardcoded array with a captured real GA trace; remove the invented `FALLBACK_TICKER` / `FALLBACK_HERO` from `HeroLiveTheorem`. Audit and fix any other invented content discovered during implementation.

Out of scope: any CI/CD that runs on GitHub-hosted infra. All build/release/deploy stays local-only via `just`, per project policy (`feedback_no_github_actions.md`).

## 2. Constraints + Decisions

| # | Decision | Rationale |
|---|---|---|
| C1 | No GitHub Actions. Cross-compile happens locally on macOS via `cargo-zigbuild`. | Standing project rule (`feedback_no_github_actions.md`). The existing `release-worker.yml` workflow is a known follow-up; this spec executes that follow-up. |
| C2 | Toolchain: `cargo-zigbuild` for `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, and `x86_64-pc-windows-gnu`. Native `cargo` for both darwin targets. | `zig` and `cargo-zigbuild` are already installed (`/opt/homebrew/bin/zig`, `~/.cargo/bin/cargo-zigbuild`). One tool covers Linux glibc, Linux musl-style portability, and Windows MinGW. No Docker, no MSVC SDK, no mingw shim. |
| C3 | Linux glibc target pinned to `2.17`. | Runs on every Linux distro from CentOS 7 / Debian 8 forward. `cargo-zigbuild` accepts the `target.glibc-version` syntax (e.g. `x86_64-unknown-linux-gnu.2.17`). |
| C4 | Windows target uses `x86_64-pc-windows-gnu` (MinGW ABI). | Pure-Rust binary, no MSVC SDK download required, no licensing surface. Works for the worker because there's no MSVC-only crate in the dep tree. |
| C5 | Five-target matrix: `linux-x86_64`, `linux-aarch64`, `darwin-x86_64`, `darwin-arm64`, `windows-x86_64`. | Existing matrix (4) + `linux-aarch64` for Graviton/Ampere/Apple-Silicon-Linux VMs. Boil-the-ocean — no platforms deferred. |
| C6 | First tag: `worker-v0.1.0`. | First public worker binary release. The "v0.4" eyebrow on the landing refers to the platform/protocol version and drifts independently. |
| C7 | License: **AGPL-3.0**. Add `LICENSE` file at repo root. | The platform has a SaaS component (`api.nasrudin.org`); AGPL-3.0's network-use clause aligns with the "open by construction" framing on the landing. The Cargo workspace `package.license` field, where present, is also updated to `"AGPL-3.0"`. |
| C8 | "No fakes" on the landing page is a hard requirement, not just for `InstallNode`. Every animated CLI / log line / ticker entry the user sees must come from a real captured worker session or a live API stream. | User instruction: "Right now it's mocked and not real log out puts." |
| C9 | The 30+ uncommitted files currently on `main` are unrelated to this release. Stash with `git stash push -u -m "pre-worker-release-WIP"` before release work; pop afterwards. | Keeps the release tag on a meaningful, focused commit chain. |

## 3. Architecture

### 3.1 Build pipeline (engine/build side)

```
                            +------------------------------+
                            |  just release-worker vX.Y.Z  |
                            +------------------------------+
                                          |
        +---------------------------------+---------------------------------+
        |                                 |                                 |
   1. preflight                    2. AI changelog                   3. confirm + tag
   - clean tree                    (existing behaviour:              + push origin TAG
   - tools present                  pipe git log to claude -p)              |
   - rustup targets installed                                               v
   - gh auth status ok                                          4. just build-worker-all
                                                                            |
            +---------------------------+----+----+-----------------+------+
            |                           |    |    |                 |
            v                           v    v    v                 v
   x86_64-unknown-linux-gnu     aarch64-...  x86_64-apple-darwin   x86_64-pc-windows-gnu
   (cargo zigbuild .glibc 2.17) (zigbuild)   (native cargo)        (cargo zigbuild)
            |                           |    |    |                 |
            +-------+-------------------+----+----+-----------------+
                    |
                    v
          5. stage bundles
          dist/nasrudin-worker-<os>-<arch>/
            ├── nasrudin-worker(.exe)
            ├── prover/   (full PhysicsGenerator + lake config)
            ├── README.md
            └── run.sh | run.ps1
                    |
                    v
          6. tar.gz / zip + sha256 sidecars
                    |
                    v
          7. gh release create worker-vX.Y.Z \
               --title "Nasrudin Worker vX.Y.Z" \
               --notes-file <ai-summary> \
               dist/*.tar.gz dist/*.zip dist/*.sha256
```

### 3.2 Frontend landing — section flow after de-mock

```
hero   — HeroLiveTheorem (live recent-theorems + SSE; NO fake fallback)
§01    — PipelineDiagram (already live)
§02    — GAViz (rewritten: replays a CAPTURED real GA trace, with worker_id + generation
                 matching the source run; no hardcoded GA_GENERATIONS)
§03    — RediscoveryGrid (already live via useFeaturedDiscoveries)
§04    — WorkerMap (already live)
§05    — TheoremBrowser (audit during impl; expected live)
§06    — RunWorker (NEW; replaces InstallNode entirely)
            • Step 1: Get a worker key   → /api-keys CTA
            • Step 2: Install Lean       → real elan one-liners (Unix + PowerShell)
            • Step 3: Download           → 3 primary cards + "Show all 5 builds" disclosure
                                            URLs: github.com/Nasdin/nasrudin/releases/latest/download/
                                            nasrudin-worker-<os>-<arch>.{tar.gz|zip}
                                            Each with .sha256 link
                                            Platform-detect via navigator.userAgent
            • Live preview: animated terminal replaying CAPTURED real ./run.sh output
                            (fixture file with timestamps; no invented lines)
            • Step 4: Extract + run      → tabs for macOS-or-Linux / Windows
            • Side rail: "What you'll need" CPU/RAM/Disk/Network panel (lifted from old InstallNode)
```

## 4. Components — detailed

### 4.1 `justfile` changes

**New recipe `build-worker-all`.** Runs preflight, then loops over the five targets, building and bundling each. Emits to `dist/`.

Pseudocode shape (real recipe written during implementation):

```
build-worker-all:
    bash:
      set -euo pipefail
      command -v zig            || die "install zig: brew install zig"
      command -v cargo-zigbuild || die "install: cargo install cargo-zigbuild"
      for T in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu \
               x86_64-apple-darwin aarch64-apple-darwin \
               x86_64-pc-windows-gnu; do
        rustup target add "$T" >/dev/null
      done
      rm -rf dist/nasrudin-worker-*
      build_one  linux   x86_64   x86_64-unknown-linux-gnu.2.17    zigbuild
      build_one  linux   aarch64  aarch64-unknown-linux-gnu.2.17   zigbuild
      build_one  darwin  x86_64   x86_64-apple-darwin              cargo
      build_one  darwin  arm64    aarch64-apple-darwin             cargo
      build_one  windows x86_64   x86_64-pc-windows-gnu            zigbuild
```

`build_one` is a shell function: `cargo (zig)build --release --target $T -p nasrudin-ga --bin worker`, then the same staging logic that exists in the current `build-worker` recipe (copy binary + prover/ + README + run.{sh,ps1}, `tar czf` or `zip -r`, `shasum -a 256`).

**Updated `release-worker vX.Y.Z`** keeps the existing flow (validate version, AI changelog, confirm) and inserts `just build-worker-all` between the user confirmation and `git tag`. After `git push origin <tag>`, calls:

```
gh release create "$TAG" \
    --title "Nasrudin Worker $VERSION" \
    --notes-file "$NOTES_FILE" \
    dist/nasrudin-worker-*.tar.gz \
    dist/nasrudin-worker-*.zip \
    dist/*.sha256
```

The recipe fails loudly (and skips the tag) if any single bundle is missing, so a partial release can never be published.

**Delete** `.github/workflows/release-worker.yml`.

The existing per-host `build-worker` recipe stays as a quick smoke build helper.

### 4.2 `LICENSE` + license metadata

- Add `LICENSE` at repo root: full AGPL-3.0 text (verbatim from gnu.org).
- Update `README.md`:
  - Fix typo `Lean4A distributed` → `Lean 4. A distributed`
  - Add a "License" section near the bottom: "AGPL-3.0. See `LICENSE`."
- Cargo workspace: where individual crate `Cargo.toml`s declare a `license` field, set to `"AGPL-3.0"`. Where they don't, leave alone (this is not a publish-to-crates.io move).

### 4.3 Frontend — `RunWorker` component (replaces `InstallNode`)

New file: `nasrudin-frontend/src/components/landing/RunWorker.tsx`.
Delete: `nasrudin-frontend/src/components/landing/InstallNode.tsx`.
Update `routes/index.tsx`: swap the `<InstallNode />` import + render for `<RunWorker />`.

**Props:** none (self-contained).

**Internal state:**
- `detectedPlatform`: `{ os: 'macos' | 'linux' | 'windows'; arch: 'x86_64' | 'aarch64' } | null`. Computed in a `useMemo` from `navigator.userAgent` + `navigator.platform` on the client; `null` during SSR.
- `showAllBuilds`: boolean (disclosure toggle).

**Constants:**
- `RELEASE_BASE = 'https://github.com/Nasdin/nasrudin/releases/latest/download'`
- `BUILDS`: array of 5 entries, each `{ os, arch, ext: 'tar.gz' | 'zip', label, archLabel }`.
- `ELAN_UNIX = "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y"`
- `ELAN_WIN  = "iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex"`
- `EXTRACT_RUN_UNIX(os, arch)` returns:
  ```
  tar xzf nasrudin-worker-<os>-<arch>.tar.gz
  cd nasrudin-worker-<os>-<arch>
  NASRUDIN_WORKER_KEY=nsk_worker_… ./run.sh
  ```
- `EXTRACT_RUN_WIN` returns:
  ```
  Expand-Archive nasrudin-worker-windows-x86_64.zip
  cd nasrudin-worker-windows-x86_64
  $env:NASRUDIN_WORKER_KEY="nsk_worker_…"; .\run.ps1
  ```

**Render outline:**

```tsx
<section id="run" class="...">
  <SectionHead num="§ 06 / 06" eyebrow="Contribute compute"
               title="Run a worker. Help physics rediscover itself."
               lede="Four steps — key, Lean, download, run. Your machine starts mutating axioms in minutes." />

  <Step n={1} title="Get a worker key">
     <p>Sign in, then open <Link to="/api-keys">/api-keys</Link> → "+ New key" → Kind: Worker.</p>
     <p>Save the <code>nsk_worker_…</code> value.</p>
     <CTA to="/api-keys">Open /api-keys →</CTA>
  </Step>

  <Step n={2} title="Install the Lean toolchain (one-time, ~200 MB)">
     <Tabs>
        <Tab label="macOS / Linux">
           <Code copyable>{ELAN_UNIX}</Code>
        </Tab>
        <Tab label="Windows (PowerShell)">
           <Code copyable>{ELAN_WIN}</Code>
        </Tab>
     </Tabs>
  </Step>

  <Step n={3} title="Download for your platform">
     <DownloadCards detected={detectedPlatform} />
     <Disclosure label={`Show all builds (${BUILDS.length})`}>
        <BuildsTable builds={BUILDS} />
     </Disclosure>
  </Step>

  <TerminalPreview fixture={runWorkerFixture} />
       {/* Animated replay of CAPTURED real ./run.sh output. Caption: */}
       {/* "Real output from ./run.sh v0.1.0, captured 2026-04-30". */}

  <Step n={4} title="Extract and run">
     <Tabs>
        <Tab label="macOS / Linux">
           <Code copyable>{EXTRACT_RUN_UNIX}</Code>
        </Tab>
        <Tab label="Windows (PowerShell)">
           <Code copyable>{EXTRACT_RUN_WIN}</Code>
        </Tab>
     </Tabs>
     <p class="margin-note">First run warms the Mathlib cache (a few minutes); next runs reuse it. Ctrl+C is clean.</p>
  </Step>

  <Aside class="install-side"> {/* lifted from old InstallNode */}
     <h3>What you'll need</h3>
     <ol class="install-reqs"> ...CPU / Memory / Disk / Network / Patience... </ol>
  </Aside>
</section>
```

**Platform detection (client-side only; SSR-safe):**

```ts
function detect(): Platform | null {
  if (typeof navigator === 'undefined') return null;
  const ua = navigator.userAgent;
  const platform = navigator.platform ?? '';
  const isMac    = /Mac/i.test(platform) || /Macintosh/i.test(ua);
  const isWin    = /Win/i.test(platform);
  const isLinux  = /Linux/i.test(platform) && !/Android/i.test(ua);
  const isArm64  = /arm64|aarch64/i.test(ua) || (isMac && /Apple\sM/i.test(ua));
  if (isMac)   return { os: 'macos',   arch: isArm64 ? 'aarch64' : 'x86_64' };
  if (isWin)   return { os: 'windows', arch: 'x86_64' };
  if (isLinux) return { os: 'linux',   arch: isArm64 ? 'aarch64' : 'x86_64' };
  return null;
}
```

Note Apple Silicon detection is best-effort — some browsers strip arch info from UA. When in doubt, default to `aarch64` for `macos` (Apple-Silicon is the default since 2020).

**`run-worker.fixture.ts`:**

```ts
export interface FixtureLine {
  text: string;
  kind: 'header' | 'info' | 'ok' | 'warn' | 'cmd' | 'output';
  /** ms after start */
  at: number;
}
export const runWorkerFixture: { capturedAt: string; binaryVersion: string; lines: FixtureLine[] };
```

Generation procedure (manual, one-time per release):

1. On a clean Mac, build the binary via `just build-worker` and extract the resulting bundle.
2. Set `NASRUDIN_API_URL=https://api.nasrudin.org NASRUDIN_WORKER_KEY=<a-real-test-worker-key>` and `./run.sh --gens 5 --pop 16 --max-lake 2`.
3. Capture `tee` output to a file for ~60 seconds, hit Ctrl+C cleanly.
4. Hand-trim to ~25 representative lines (header banner, axiom-store summary, elaborator boot, first 2-3 generations with real op names + real timings, one ingest line, one heartbeat).
5. Convert to `FixtureLine[]` with `at` offsets that match real wall-clock spacing (clamped to a max of ~12s of replay so the section doesn't drag).
6. Save under `nasrudin-frontend/src/components/landing/run-worker.fixture.ts` with a `capturedAt` ISO timestamp + `binaryVersion: 'v0.1.0'`.

**`<TerminalPreview>`** is a small component (~80 LOC) that animates `lines` based on `at`, styled to match the existing `.install-cli` CSS (we're reusing the visual treatment, only the content changes). It loops once finished — but with a subtle "captured" badge in the corner so it's clear this is a recording, not a live feed.

### 4.4 Frontend — `GAViz` rewrite

The current `GAViz.tsx` has an 8-row hardcoded `GA_GENERATIONS` array and a fake `worker · home-pc-aklint` ID and a fake "Generation 4,218,107" counter. Replace with a captured real GA cycle, sourced from the same fixture-capture run:

- New file: `nasrudin-frontend/src/components/landing/ga-viz.fixture.ts` exporting a real GA trace `{ workerId: string; generationStart: number; rows: GaRow[] }` where each `GaRow` is `{ op: 'mutate' | 'crossover' | 'compose' | 'axiom'; expr: string; status: 'seed' | 'accepted' | 'rejected'; result: string }`. Captured from a real run that produced the SR `F = ma`-style ladder (or whichever ladder the worker actually traversed during the capture session).
- `GAViz.tsx` reads from the fixture instead of the inline array.
- The eyebrow becomes "Generation N · captured trace" where `N` matches the real source.
- The worker id becomes the real worker_id from the capture (or a deterministic anonymised slug like `worker · capture-2026-04-30` if showing a real hostname is undesirable).

**Stretch (only if low cost):** if the engine already emits per-generation events on an SSE channel like `/api/events/ga_traces`, replace the fixture with a live subscription that falls back to the fixture when the connection is silent. Decision deferred to plan-writing — implementation will check whether such an endpoint exists before deciding.

### 4.5 Frontend — `HeroLiveTheorem` ticker fallback

Currently has `FALLBACK_TICKER` (6 invented `VERIFIED  thm:9f3a2c …` lines) + `FALLBACK_HERO` (Schwarz inequality placeholder) shown before the SSE/REST data arrives. Replace with:

- Initial state: empty ticker + "*waiting for live events…*" caption.
- On mount: REST-fetch the most recent verified theorems via `useRecentTheorems(8)`. As soon as data arrives, seed the ticker with `VERIFIED thm:<id-prefix> <statement>` derived from real theorems.
- SSE updates prepend new lines on top of that real-data baseline.
- If both REST and SSE silently fail (offline), the caption stays as "*waiting for live events…*"; never invent lines.
- `FALLBACK_HERO` removed entirely. The hero card shows a skeleton/spinner until the first real theorem lands.

### 4.6 Other landing components — audit

During implementation, verify each of the following emits only data sourced from a real backend / real capture:

- `PipelineDiagram.tsx` — receives stat props; verify the props in `index.tsx` come from `useStats()` (currently look correct).
- `RediscoveryGrid.tsx` — uses `useFeaturedDiscoveries()` (live).
- `TheoremBrowser.tsx` — verify it uses live queries; if any hardcoded sample rows linger, replace with live `useRecentTheorems` data.
- `WorkerMap.tsx` — uses `useWorkers()` (live).

Any further fakes uncovered get fixed in the same PR rather than deferred.

## 5. Data flow

### 5.1 Build → Release

```
local Mac        Rust source           target/{T}/release/worker(.exe)
                       │
                       ▼
                cargo-zigbuild      glibc-pinned .so links / mingw .exe
                       │
                       ▼
                stage dist/<pkg>/   binary + prover/ + README + run script
                       │
                       ▼
                tar.gz / zip + sha256
                       │
                       ▼
              gh release upload    GitHub release worker-vX.Y.Z assets
                       │
                       ▼
               releases/latest/download/nasrudin-worker-<os>-<arch>.{tar.gz|zip}
                       │
                       ▼
                   end user        downloads, extracts, runs
```

### 5.2 Worker runtime (unchanged — no engine changes in this spec)

```
./run.sh
  ├── env check (NASRUDIN_WORKER_KEY)
  ├── lake on PATH check
  ├── prover/.lake exists? else `lake exe cache get`
  └── exec ./nasrudin-worker --verify ./prover ...
        ├── prints banner + axiom store summary
        ├── boots persistent Lean elaborator
        ├── runs GA chunks (mutate/crossover/compose)
        ├── lake-builds top novel candidates per chunk
        ├── POSTs verified discoveries to api.nasrudin.org/api/ingest
        ├── re-syncs /api/seed at chunk boundaries
        └── heartbeats periodically
```

### 5.3 Frontend — RunWorker section data

```
RELEASE_BASE = 'https://github.com/Nasdin/nasrudin/releases/latest/download'
              │
              ▼
  computed download URLs (5 SKUs)  ←  click
              │
              ▼
  GitHub redirects to the artifact for `latest`
              │
              ▼
  user follows the on-page Step 4 instructions
              │
              ▼
  binary connects to api.nasrudin.org with their worker key
```

`run-worker.fixture.ts` and `ga-viz.fixture.ts` are static imports — bundled at build time, no runtime fetch.

## 6. Error handling + edge cases

- **Build fails for one target.** `just build-worker-all` aborts with a non-zero exit before tagging, so a release with a missing platform never gets published. The error message names the failing target so the operator can fix and retry.
- **`gh release create` fails after tag is pushed.** The tag is already on `origin`. The recipe prints an explicit recovery hint: "tag pushed but release upload failed; re-run `gh release create worker-vX.Y.Z dist/...` to retry, or `git push --delete origin worker-vX.Y.Z` and `git tag -d worker-vX.Y.Z` to abort."
- **User on platform we don't ship binaries for** (e.g. FreeBSD, RISC-V, Windows ARM64). The "Show all builds" disclosure makes it clear what's available. The default download cards still show the three primary platforms; detection just doesn't highlight any of them.
- **Apple Silicon UA detection fails** (some browsers report `Intel`). Default Mac to `aarch64` since Apple-Silicon is the default since 2020; surface both as visible alternatives in the disclosure so an Intel-Mac user can pick the right SKU.
- **SSR / pre-hydration.** Platform detection returns `null` server-side; the section renders without a "(detected)" highlight, then the client hydrates and adds the highlight. No layout shift — the highlight is a coloured border, not a size change.
- **Empty `./run.sh` fixture / parsing error.** `<TerminalPreview>` has a guard: if the fixture is empty or malformed, show a static "Live output" placeholder card linking to the worker README rather than crashing.
- **API down / SSE unreachable.** Hero ticker shows "*waiting for live events…*", `HeroLiveTheorem` shows a skeleton card, `GAViz` falls through to its captured fixture. No fakes anywhere.
- **`worker-v0.1.0` tag already exists.** Existing `release-worker` recipe already guards against this (`git rev-parse "$TAG"` check).
- **In-flight uncommitted work.** Existing dirty-tree guard remains. Operator runs `git stash push -u -m "pre-release-WIP"` before invoking `release-worker`, then `git stash pop` after success. Documented in a new "Cutting a release" section in `README.md`.

## 7. Testing

The brainstorming-skill principle here is: every claim the spec makes about end-to-end behaviour must be testable, and the release pipeline isn't done until those tests have actually run.

| Layer | Test |
|---|---|
| Build pipeline | `just build-worker-all` runs to completion on this Mac. Each of the 5 bundles exists in `dist/`, has a sibling `.sha256`, and the recorded sha256 matches a fresh `shasum -a 256`. |
| Linux binary | Extract `nasrudin-worker-linux-x86_64.tar.gz` on a Linux host (cloud VM or Docker `ubuntu:22.04` image). `./run.sh` boots, prints the banner, and (with a real worker key) reaches `▶ API submission target: …` line. |
| Windows binary | Extract the `.zip` on a Windows host (or via wine/UTM). `run.ps1` boots, hits the same banner. (If no Windows host accessible during the release: at minimum `file dist/.../nasrudin-worker.exe` reports a sane PE32+ executable, and `wine ./nasrudin-worker.exe --help` exits 0.) |
| macOS binaries | `./run.sh --help` works on both `aarch64` and (if accessible) `x86_64` macOS. |
| Frontend RunWorker | Vitest unit tests for the platform-detection function: cases for macOS-Apple-Silicon, macOS-Intel, Windows-x86_64, Linux-x86_64, Linux-aarch64, Android (returns `null`), undefined navigator (SSR). |
| Frontend RunWorker | Visual smoke test in dev: detected card highlights correctly; disclosure expands; tabs switch; copy buttons populate clipboard; download links resolve via `gh release view` to the actual asset URLs. |
| Frontend GAViz / HeroLiveTheorem | Vitest unit tests verifying no `FALLBACK_TICKER` / `FALLBACK_HERO` literal strings remain in the rendered output when the queries are pending. |
| End-to-end | After release: open `https://nasrudin.org`, follow Step 1 → Step 4 on a clean machine using ONLY what's on the landing page (no other docs). Confirm the worker registers, heartbeats, and submits at least one verified discovery. |

## 8. Implementation order

(For the writing-plans hand-off — not an exhaustive plan, but the recommended sequencing.)

1. Stash in-flight work on `main`.
2. Add `LICENSE` (AGPL-3.0) + fix README typo. Commit.
3. New `just build-worker-all` recipe + helper script. Verify all 5 bundles build from a clean tree. Commit.
4. Update `just release-worker` to call the new recipe + `gh release create`. Delete `.github/workflows/release-worker.yml`. Commit.
5. Capture real `./run.sh` log fixture + GAViz trace fixture by running a worker against the live API. Commit fixtures.
6. New `RunWorker.tsx` + `TerminalPreview.tsx`. Wire into `index.tsx`. Delete `InstallNode.tsx`. Vitest for platform detection.
7. Rewrite `GAViz.tsx` to consume the captured fixture (and optional SSE upgrade if the endpoint exists).
8. Strip `FALLBACK_TICKER` + `FALLBACK_HERO` from `HeroLiveTheorem.tsx`; replace with skeleton + REST-seeded ticker.
9. Audit pass: read every other landing component and confirm no invented data leaks through.
10. Pre-flight checklist: `just check`, `just test-frontend`, `just build-worker-all`, manual local browse, `gh auth status`.
11. Cut `worker-v0.1.0` via `just release-worker v0.1.0`. Walk Step 1 → Step 4 on a clean test machine.
12. Pop the stash; resume in-flight work.

## 9. Open questions / TBD during planning

- Whether to add a live SSE-driven mode for `GAViz` on top of the captured fixture (depends on whether `/api/events/ga_traces` or similar already exists; I'll grep during plan-writing).
- Whether to surface the SHA256 inline in the download cards or only behind the disclosure. Default: only behind disclosure to keep the cards clean. Reconsider if we get user feedback that verifying checksums is expected behaviour for the audience.

Nothing in this list blocks implementation — these are tactical refinements decided during execution.

## 10. Summary

End-to-end: a user lands on `nasrudin.org`, sees a four-step download-and-run UX showing real output from the actual worker binary, clicks the auto-detected platform card, downloads a tarball that was cross-compiled locally on a Mac and uploaded to `github.com/Nasdin/nasrudin/releases/tag/worker-v0.1.0`, follows three commands, and joins the network. Every animation on the landing replays a captured real session or a live API stream — nothing invented. No GitHub Actions involved at any step.
