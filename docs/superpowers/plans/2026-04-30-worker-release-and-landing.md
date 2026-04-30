# Worker `v0.1.0` Release + Landing-Page De-Mock — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Cut the first public worker binary release (`worker-v0.1.0`) on `github.com/Nasdin/nasrudin` via local cross-compile (no GH Actions), and replace every mocked CLI / log fixture / event ticker on the landing with output captured from the actual worker binary or from the live API.

**Architecture:** Two coupled surfaces. (1) A new `just build-worker-all` recipe uses `cargo-zigbuild` to produce five platform bundles on this Mac (linux-x86_64, linux-aarch64, darwin-x86_64, darwin-arm64, windows-x86_64); the existing `just release-worker` is rewired to call it and then `gh release create`. The existing GH Actions workflow is deleted. (2) The frontend landing page replaces `InstallNode` with a real four-step `RunWorker` section + animated terminal preview replaying captured `./run.sh` output, rewrites `GAViz` to consume a captured real GA trace, and strips the invented `FALLBACK_TICKER` / `FALLBACK_HERO` from `HeroLiveTheorem`.

**Tech Stack:** Rust (cargo-zigbuild, zig 0.x); GitHub CLI (`gh`); justfile; TanStack Start frontend (React 19, TanStack Query 5); Vitest 3 for unit tests; AGPL-3.0.

**Spec:** `docs/superpowers/specs/2026-04-30-worker-release-and-landing-design.md`

---

## File Structure

**Repo root**

| Path | Status | Responsibility |
|---|---|---|
| `LICENSE` | new | Verbatim AGPL-3.0 text. |
| `README.md` | modify | Fix `Lean4A distributed` typo; add License section. Document `just release-worker` flow + stash convention. |
| `justfile` | modify | Replace per-host `build-worker` flow with `build-worker-all`; rewire `release-worker` to build locally + `gh release create`. |
| `.github/workflows/release-worker.yml` | delete | Replaced by local cross-compile. |
| `deploy/scripts/build-worker-bundle.sh` | new | Helper invoked by `build-worker-all`: stages one platform bundle (binary + prover/ + README + run script) + tarballs/zips + sha256. |
| `deploy/worker-bundle/run.sh` | unchanged | Already correct. |
| `deploy/worker-bundle/run.ps1` | unchanged | Already correct. |
| `deploy/worker-bundle/README.md` | unchanged | Already correct. |

**Frontend — TypeScript / React**

| Path | Status | Responsibility |
|---|---|---|
| `nasrudin-frontend/package.json` | modify | Add `jsdom` and `@testing-library/react` dev deps; add `vitest.config.ts`. |
| `nasrudin-frontend/vitest.config.ts` | new | Configure jsdom env so component tests can render. |
| `nasrudin-frontend/src/components/landing/RunWorker.tsx` | new | Replaces `InstallNode`. Four numbered steps + terminal preview + side rail. |
| `nasrudin-frontend/src/components/landing/RunWorker.platform.ts` | new | Pure platform-detection function. Easily unit-testable, no React. |
| `nasrudin-frontend/src/components/landing/RunWorker.platform.test.ts` | new | Vitest unit tests for platform detection. |
| `nasrudin-frontend/src/components/landing/TerminalPreview.tsx` | new | Animated terminal that replays a captured-log fixture. |
| `nasrudin-frontend/src/components/landing/run-worker.fixture.ts` | new | Real `./run.sh` output captured from a live worker run; typed `FixtureLine[]`. |
| `nasrudin-frontend/src/components/landing/ga-viz.fixture.ts` | new | Real GA trace captured from the same live worker run. |
| `nasrudin-frontend/src/components/landing/InstallNode.tsx` | delete | Replaced by `RunWorker`. |
| `nasrudin-frontend/src/components/landing/GAViz.tsx` | modify | Consume `ga-viz.fixture.ts` instead of inline `GA_GENERATIONS` array. |
| `nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx` | modify | Remove `FALLBACK_TICKER` + `FALLBACK_HERO`; show "waiting for live events…" until real data arrives. |
| `nasrudin-frontend/src/routes/index.tsx` | modify | Swap `<InstallNode />` import for `<RunWorker />`. |
| `nasrudin-frontend/src/styles/styles.css` | modify | Add `.run-worker-*` styles for the new download cards + step layout. Reuse `.install-cli` styles for `TerminalPreview`. |

**Capture artifacts (one-time, manual operator step — see Task 9)**

| Path | Status | Responsibility |
|---|---|---|
| `dist/captures/run-worker.log` | new (committed) | Raw `./run.sh` stdout from the capture session. Source-of-truth for `run-worker.fixture.ts`. |
| `dist/captures/ga-trace.log` | new (committed) | Raw GA-cycle trace from the capture session. Source-of-truth for `ga-viz.fixture.ts`. |

---

## Phase 0 — Pre-flight

### Task 0: Stash in-flight work and verify clean tree

**Files:** none modified — this is operator state hygiene.

- [ ] **Step 0.1: Verify we're on `main` and remote is correct**

```bash
git rev-parse --abbrev-ref HEAD
git remote get-url origin
```

Expected: `main` and `git@github.com:Nasdin/nasrudin.git`.

- [ ] **Step 0.2: Stash uncommitted work**

```bash
git stash push -u -m "pre-worker-release-WIP"
git status --porcelain
```

Expected: empty output (clean tree).

- [ ] **Step 0.3: Verify remote is reachable + `gh` is authenticated**

```bash
git fetch origin
gh auth status
```

Expected: `gh` reports a logged-in account with repo write access to `Nasdin/nasrudin`.

> NOTE: Do NOT pop the stash until Phase 7 completes. All release work commits onto `main` on top of the stashed state.

---

## Phase 1 — Repo public-readiness

### Task 1: Add AGPL-3.0 LICENSE file

**Files:**
- Create: `LICENSE`

- [ ] **Step 1.1: Download canonical AGPL-3.0 text**

```bash
curl -sSfL https://www.gnu.org/licenses/agpl-3.0.txt -o LICENSE
wc -l LICENSE
```

Expected: ~661 lines. Check the first line is `                    GNU AFFERO GENERAL PUBLIC LICENSE`.

- [ ] **Step 1.2: Verify the file is exactly the standard text**

```bash
head -3 LICENSE
shasum -a 256 LICENSE
```

Expected: header reads `GNU AFFERO GENERAL PUBLIC LICENSE / Version 3, 19 November 2007 / Copyright (C) 2007 Free Software Foundation, Inc. <https://fsf.org/>`. Note the sha256 — useful if anyone questions the file later.

- [ ] **Step 1.3: Commit**

```bash
git add LICENSE
git commit -m "chore: add AGPL-3.0 LICENSE"
```

### Task 2: Update README — typo + license section + release docs

**Files:**
- Modify: `README.md`

- [ ] **Step 2.1: Fix the `Lean4A distributed` typo**

Find the existing string `Lean4A distributed theorem generation engine` and replace with `Lean 4. A distributed theorem generation engine`.

- [ ] **Step 2.2: Append a License section near the bottom**

Add (above the final closing remarks, or as the last `##` section):

```markdown
## License

AGPL-3.0. See [`LICENSE`](./LICENSE).

The platform has a SaaS component (`api.nasrudin.org`) — the network-use clause means anyone running modified versions as a hosted service must publish their changes.
```

- [ ] **Step 2.3: Append a "Cutting a worker release" section**

```markdown
## Cutting a worker release

All cross-platform worker binaries are built locally on macOS via `just`; we do not use GitHub Actions for release builds.

```bash
# Stash any in-flight work first (release-worker requires a clean tree):
git stash push -u -m "pre-release-WIP"

# Cut the release. Builds Linux x86_64/aarch64, macOS x86_64/arm64, and
# Windows x86_64 locally via cargo-zigbuild, then uploads to GitHub.
just release-worker v0.1.0

# Pop your in-flight work:
git stash pop
```

Prerequisites: `zig` and `cargo-zigbuild` installed (`brew install zig && cargo install cargo-zigbuild`); `gh auth status` shows write access to `Nasdin/nasrudin`; all five rustup targets installed (the recipe will add them automatically).
```

- [ ] **Step 2.4: Commit**

```bash
git add README.md
git commit -m "docs: fix typo, add License + release-cutting sections"
```

---

## Phase 2 — Build pipeline

### Task 3: Install missing rustup targets (idempotent)

**Files:** none — environment setup.

- [ ] **Step 3.1: Add the four cross-compile targets**

```bash
rustup target add \
  x86_64-unknown-linux-gnu \
  aarch64-unknown-linux-gnu \
  x86_64-apple-darwin \
  x86_64-pc-windows-gnu
rustup target list --installed
```

Expected: list contains all five targets (`aarch64-apple-darwin` was already present, the four above are now added).

- [ ] **Step 3.2: Verify zigbuild + zig + gh + shasum are available**

```bash
zig version
cargo zigbuild --version
gh --version
shasum --version
```

Expected: all four print versions and exit 0. If any are missing, install via `brew install zig gh` / `cargo install cargo-zigbuild`.

### Task 4: Add `deploy/scripts/build-worker-bundle.sh` helper

**Files:**
- Create: `deploy/scripts/build-worker-bundle.sh`

- [ ] **Step 4.1: Write the helper script**

```bash
#!/usr/bin/env bash
# Stage and archive a single Nasrudin discovery-worker bundle.
#
# Usage: build-worker-bundle.sh <os> <arch> <rust-target>
#   os:          one of {linux, darwin, windows}
#   arch:        one of {x86_64, aarch64, arm64}
#   rust-target: rust target triple, possibly with .glibc-version suffix
#
# Outputs into dist/:
#   dist/nasrudin-worker-<os>-<arch>/
#   dist/nasrudin-worker-<os>-<arch>.{tar.gz|zip}
#   dist/nasrudin-worker-<os>-<arch>.{tar.gz|zip}.sha256

set -euo pipefail

OS="$1"
ARCH="$2"
RUST_TARGET="$3"

PKG="nasrudin-worker-${OS}-${ARCH}"
OUT="dist/${PKG}"

# Strip any zigbuild glibc suffix (e.g. "x86_64-unknown-linux-gnu.2.17") to get
# the actual rustc triple used for the target/<triple>/release/ output dir.
TRIPLE="${RUST_TARGET%.*}"
case "$RUST_TARGET" in
  *.*) USE_ZIGBUILD=1 ;;
  *)
    case "$RUST_TARGET" in
      *-linux-gnu|*-linux-musl|*-windows-gnu) USE_ZIGBUILD=1 ;;
      *) USE_ZIGBUILD=0 ;;
    esac
    ;;
esac

echo "[bundle] building ${PKG} (target=${RUST_TARGET}, zigbuild=${USE_ZIGBUILD})"

if [ "$USE_ZIGBUILD" = "1" ]; then
  (cd engine && cargo zigbuild --release \
      --target "$RUST_TARGET" -p nasrudin-ga --bin worker)
else
  (cd engine && cargo build --release \
      --target "$RUST_TARGET" -p nasrudin-ga --bin worker)
fi

rm -rf "$OUT"
mkdir -p "$OUT/prover"

if [ "$OS" = "windows" ]; then
  cp "engine/target/${TRIPLE}/release/worker.exe" "$OUT/nasrudin-worker.exe"
else
  cp "engine/target/${TRIPLE}/release/worker"     "$OUT/nasrudin-worker"
fi

cp -R prover/PhysicsGenerator "$OUT/prover/"
cp prover/PhysicsGenerator.lean prover/lakefile.lean prover/lake-manifest.json prover/lean-toolchain "$OUT/prover/"
cp deploy/worker-bundle/README.md "$OUT/README.md"

if [ "$OS" = "windows" ]; then
  cp deploy/worker-bundle/run.ps1 "$OUT/run.ps1"
else
  cp deploy/worker-bundle/run.sh  "$OUT/run.sh"
  chmod +x "$OUT/run.sh" "$OUT/nasrudin-worker"
fi

if [ "$OS" = "windows" ]; then
  (cd dist && rm -f "${PKG}.zip" && zip -qr "${PKG}.zip" "${PKG}")
  (cd dist && shasum -a 256 "${PKG}.zip" > "${PKG}.zip.sha256")
  echo "[bundle] -> dist/${PKG}.zip"
else
  (cd dist && tar czf "${PKG}.tar.gz" "${PKG}")
  (cd dist && shasum -a 256 "${PKG}.tar.gz" > "${PKG}.tar.gz.sha256")
  echo "[bundle] -> dist/${PKG}.tar.gz"
fi
```

- [ ] **Step 4.2: Make it executable**

```bash
chmod +x deploy/scripts/build-worker-bundle.sh
```

- [ ] **Step 4.3: Commit**

```bash
git add deploy/scripts/build-worker-bundle.sh
git commit -m "build: add build-worker-bundle.sh staging helper"
```

### Task 5: Add `just build-worker-all` recipe

**Files:**
- Modify: `justfile` (insert below the existing `build-worker` recipe)

- [ ] **Step 5.1: Add the recipe**

Insert (immediately after the current `build-worker:` recipe, before `release-worker version:`):

```just
# Build the public discovery worker tarballs/zip for ALL supported targets
# locally on this Mac via cargo-zigbuild. Outputs five bundles into dist/.
build-worker-all:
    #!/usr/bin/env bash
    set -euo pipefail
    cd {{justfile_directory()}}

    # Pre-flight
    command -v zig            >/dev/null || { echo "error: zig not on PATH (brew install zig)" >&2; exit 1; }
    command -v cargo-zigbuild >/dev/null || { echo "error: cargo-zigbuild not on PATH (cargo install cargo-zigbuild)" >&2; exit 1; }
    command -v gh             >/dev/null || { echo "error: gh CLI not on PATH (brew install gh)" >&2; exit 1; }

    for T in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu \
             x86_64-apple-darwin aarch64-apple-darwin \
             x86_64-pc-windows-gnu; do
      rustup target add "$T" >/dev/null
    done

    rm -rf dist/nasrudin-worker-*

    deploy/scripts/build-worker-bundle.sh linux   x86_64  "x86_64-unknown-linux-gnu.2.17"
    deploy/scripts/build-worker-bundle.sh linux   aarch64 "aarch64-unknown-linux-gnu.2.17"
    deploy/scripts/build-worker-bundle.sh darwin  x86_64  "x86_64-apple-darwin"
    deploy/scripts/build-worker-bundle.sh darwin  arm64   "aarch64-apple-darwin"
    deploy/scripts/build-worker-bundle.sh windows x86_64  "x86_64-pc-windows-gnu"

    echo
    echo "═════════════════ build-worker-all complete ═════════════════"
    ls -1 dist/nasrudin-worker-*.tar.gz dist/nasrudin-worker-*.zip 2>/dev/null
    echo "═════════════════════════════════════════════════════════════"
```

- [ ] **Step 5.2: Smoke-test the recipe builds at least one target end-to-end**

Run the helper for the native darwin-arm64 target only first — fast, catches scripting bugs without a full 5-target rebuild.

```bash
deploy/scripts/build-worker-bundle.sh darwin arm64 aarch64-apple-darwin
ls -1 dist/nasrudin-worker-darwin-arm64.tar.gz dist/nasrudin-worker-darwin-arm64.tar.gz.sha256
shasum -a 256 -c dist/nasrudin-worker-darwin-arm64.tar.gz.sha256
```

Expected: `dist/nasrudin-worker-darwin-arm64.tar.gz` exists, `.sha256` exists, and `shasum -c` reports `OK`.

- [ ] **Step 5.3: Run the full five-target build**

```bash
just build-worker-all
ls -1 dist/nasrudin-worker-*.tar.gz dist/nasrudin-worker-*.zip
```

Expected: 4 `.tar.gz` files (linux x2, darwin x2) and 1 `.zip` (windows). Total 5 bundles. All 5 `.sha256` sidecars too.

- [ ] **Step 5.4: Sanity-check binary architecture for each target**

```bash
file dist/nasrudin-worker-linux-x86_64/nasrudin-worker
file dist/nasrudin-worker-linux-aarch64/nasrudin-worker
file dist/nasrudin-worker-darwin-x86_64/nasrudin-worker
file dist/nasrudin-worker-darwin-arm64/nasrudin-worker
file dist/nasrudin-worker-windows-x86_64/nasrudin-worker.exe
```

Expected, respectively: `ELF 64-bit LSB ... x86-64`, `ELF 64-bit LSB ... ARM aarch64`, `Mach-O 64-bit executable x86_64`, `Mach-O 64-bit executable arm64`, `PE32+ executable (console) x86-64, for MS Windows`.

- [ ] **Step 5.5: Commit**

```bash
git add justfile
git commit -m "build: just build-worker-all — local 5-target cross-compile via zigbuild"
```

### Task 6: Rewire `just release-worker` to call `build-worker-all` + `gh release create`

**Files:**
- Modify: `justfile` (the existing `release-worker version:` recipe)

- [ ] **Step 6.1: Replace the recipe tail**

Locate the existing `release-worker version:` recipe. Keep the existing version validation, dirty-tree check, AI changelog generation, and confirmation prompt UNCHANGED. The existing recipe ends with five lines that look like:

```just
    git tag -a "$TAG" -F "$NOTES_FILE"
    git push origin "$TAG"
    echo "[release] pushed $TAG; CI will build + publish at:"
    echo "    https://github.com/Nasdin/nasrudin/actions"
    echo "    https://github.com/Nasdin/nasrudin/releases/tag/${TAG}"
```

Replace those five lines with:

```just
    # Build all five bundles BEFORE tagging — if any target fails, no tag, no release.
    echo "[release] building all worker bundles locally..."
    just build-worker-all

    # Sanity check: 5 archives + 5 sha256 sidecars must exist.
    expected_archives=(
      dist/nasrudin-worker-linux-x86_64.tar.gz
      dist/nasrudin-worker-linux-aarch64.tar.gz
      dist/nasrudin-worker-darwin-x86_64.tar.gz
      dist/nasrudin-worker-darwin-arm64.tar.gz
      dist/nasrudin-worker-windows-x86_64.zip
    )
    for f in "${expected_archives[@]}"; do
      [ -s "$f" ]        || { echo "error: missing archive $f" >&2; exit 1; }
      [ -s "$f.sha256" ] || { echo "error: missing sha256 sidecar $f.sha256" >&2; exit 1; }
    done

    git tag -a "$TAG" -F "$NOTES_FILE"
    git push origin "$TAG"
    echo "[release] pushed $TAG"

    echo "[release] creating GitHub release..."
    gh release create "$TAG" \
        --title "Nasrudin Worker {{version}}" \
        --notes-file "$NOTES_FILE" \
        "${expected_archives[@]}" \
        dist/nasrudin-worker-*.sha256

    echo "[release] published:"
    echo "    https://github.com/Nasdin/nasrudin/releases/tag/${TAG}"
```

- [ ] **Step 6.2: Delete the GitHub Actions workflow**

```bash
git rm .github/workflows/release-worker.yml
ls .github/workflows/ 2>/dev/null
```

Expected: directory empty (or doesn't exist). If empty, also remove the directory.

```bash
[ -d .github/workflows ] && [ -z "$(ls -A .github/workflows)" ] && rmdir .github/workflows
ls .github/
```

Expected: only `FUNDING.yml` remains under `.github/`.

- [ ] **Step 6.3: Commit**

```bash
git add justfile .github/
git commit -m "build: release-worker now builds locally + uploads via gh; drop GH Actions"
```

---

## Phase 3 — Capture real worker output

### Task 7: Verify the worker binary connects against `api.nasrudin.org`

**Files:** none — runtime check.

- [ ] **Step 7.1: Confirm a worker key is available**

You need an `nsk_worker_…` key for `api.nasrudin.org`. If you don't have one, sign in at <https://nasrudin.org/signin> → /api-keys → "+ New key" → Kind: Worker. Save the value to a local file *outside the repo* (e.g. `~/.nasrudin-worker-key`). Never commit it.

- [ ] **Step 7.2: Verify the locally-built darwin-arm64 binary boots and reaches the API**

```bash
cd dist/nasrudin-worker-darwin-arm64
NASRUDIN_API_URL=https://api.nasrudin.org \
NASRUDIN_WORKER_KEY="$(cat ~/.nasrudin-worker-key)" \
NASRUDIN_WORKER_ID=capture-2026-04-30 \
./run.sh --gens 3 --pop 16 --max-lake 2 \
  | tee /tmp/run-worker-smoke.log
```

Expected: prints the banner (`═══ Nasrudin Spontaneous Physics Discovery — domain=sr ═══`), reports `▶ API submission target: https://api.nasrudin.org`, prints axiom-store summary, boots elaborator, runs at least one generation, exits cleanly when the requested generations finish (or on Ctrl+C). No `error:` lines.

If this fails: investigate before continuing — Phase 3 captures depend on the binary working end-to-end against production.

```bash
cd ../..
```

### Task 8: Capture the `./run.sh` log fixture

**Files:**
- Create: `dist/captures/run-worker.log`

- [ ] **Step 8.1: Create the captures directory**

```bash
mkdir -p dist/captures
```

- [ ] **Step 8.2: Run the worker for ~60s and capture stdout**

```bash
cd dist/nasrudin-worker-darwin-arm64
NASRUDIN_API_URL=https://api.nasrudin.org \
NASRUDIN_WORKER_KEY="$(cat ~/.nasrudin-worker-key)" \
NASRUDIN_WORKER_ID=capture-2026-04-30 \
RUST_LOG=info \
./run.sh --gens 5 --pop 32 --max-lake 4 \
  2>&1 | tee ../../dist/captures/run-worker.log
cd ../..
```

Stop the worker (Ctrl+C is clean) once the log shows: banner + axiom store summary + persistent elaborator boot + at least 2-3 generations with real `op` results + at least one HTTP submit / heartbeat line. Around 60-90 seconds of wall-clock is sufficient.

- [ ] **Step 8.3: Verify the capture is non-empty + commit it**

```bash
wc -l dist/captures/run-worker.log
head -30 dist/captures/run-worker.log
git add dist/captures/run-worker.log
git commit -m "fixture: real ./run.sh capture for landing-page TerminalPreview"
```

Expected: at least 50 lines; banner visible at the top.

### Task 9: Capture the GA-trace fixture

**Files:**
- Create: `dist/captures/ga-trace.log`

> If the `run-worker.log` capture in Task 8 already contains rich per-generation rows (lines like `[gen N·M] mutate → … verified · …s` or similar), it can also serve as the GA-trace source — Task 11 will extract from it directly. Otherwise, run a longer capture with more verbose logging.

- [ ] **Step 9.1: Inspect the existing capture for GA-cycle lines**

```bash
grep -E "gen [0-9]" dist/captures/run-worker.log | head -20
grep -E "mutate|crossover|compose|verified|rejected" dist/captures/run-worker.log | head -20
```

If at least 8 GA-row lines are present, copy them to a separate file as the GA-trace source:

```bash
grep -E "gen [0-9]|mutate|crossover|compose|verified|rejected" dist/captures/run-worker.log \
  > dist/captures/ga-trace.log
wc -l dist/captures/ga-trace.log
```

Otherwise, do a longer capture run targeting GA verbosity:

```bash
cd dist/nasrudin-worker-darwin-arm64
NASRUDIN_API_URL=https://api.nasrudin.org \
NASRUDIN_WORKER_KEY="$(cat ~/.nasrudin-worker-key)" \
NASRUDIN_WORKER_ID=capture-2026-04-30 \
RUST_LOG=info,nasrudin_ga=debug \
./run.sh --gens 10 --pop 64 --max-lake 6 \
  2>&1 | tee ../../dist/captures/ga-trace.log
cd ../..
```

- [ ] **Step 9.2: Commit**

```bash
git add dist/captures/ga-trace.log
git commit -m "fixture: real GA-trace capture for landing-page GAViz"
```

---

## Phase 4 — Frontend test infrastructure

### Task 10: Add Vitest config (jsdom env not strictly needed — keep it pure-Node)

**Files:**
- Create: `nasrudin-frontend/vitest.config.ts`

> The platform-detection function is pure (it stubs `navigator`), so jsdom is unnecessary. Keep the config minimal — node env, no jsdom dependency. If component-level tests are added later, jsdom can be installed then.

- [ ] **Step 10.1: Write the config**

```ts
import { defineConfig } from 'vitest/config';
import tsconfigPaths from 'vite-tsconfig-paths';

export default defineConfig({
  plugins: [tsconfigPaths()],
  test: {
    environment: 'node',
    include: ['src/**/*.test.ts', 'src/**/*.test.tsx'],
  },
});
```

- [ ] **Step 10.2: Verify Vitest picks it up**

```bash
cd nasrudin-frontend && pnpm test --run --reporter=verbose 2>&1 | tail -10
cd ..
```

Expected: `No test files found, exiting with code 1` or `0 tests` — that's fine, we haven't written any yet. The point is the config loads without errors.

- [ ] **Step 10.3: Commit**

```bash
git add nasrudin-frontend/vitest.config.ts
git commit -m "frontend: add minimal vitest config (node env)"
```

---

## Phase 5 — Frontend RunWorker section (TDD)

### Task 11: Author fixtures from captured logs

**Files:**
- Create: `nasrudin-frontend/src/components/landing/run-worker.fixture.ts`
- Create: `nasrudin-frontend/src/components/landing/ga-viz.fixture.ts`

This task converts the raw captures into typed TS fixtures by hand-trimming. Both fixtures must contain ONLY lines that appeared in the captures (verbatim text, optionally with the worker_id replaced by a stable slug for privacy).

- [ ] **Step 11.1: Pick ~25 representative lines from `dist/captures/run-worker.log`**

Open `dist/captures/run-worker.log`. Select a contiguous-ish subset that tells the full story: banner, API target line, axiom-store summary header + 3-4 axiom names + the no-cheat audit line, persistent-elaborator boot, the "▶ Running discovery: …" line, 4-6 actual GA-row lines (mutate/crossover/compose with their real exprs and timings), one ingest/submit line, one heartbeat.

Aim for ~25 lines total. Do NOT invent lines. If a line in the capture mentions the actual hostname, replace `capture-2026-04-30` with a generic slug (the env var `NASRUDIN_WORKER_ID=capture-2026-04-30` should already have made this consistent).

- [ ] **Step 11.2: Write `run-worker.fixture.ts`**

```ts
// Real ./run.sh output captured 2026-04-30 from a worker bundled in
// nasrudin-worker-v0.1.0 against api.nasrudin.org. Source-of-truth log:
// dist/captures/run-worker.log (committed). Lines are verbatim except the
// worker_id, which was set to "capture-2026-04-30" via env var.

export type FixtureLineKind = 'header' | 'info' | 'ok' | 'warn' | 'cmd' | 'output';

export interface FixtureLine {
  text: string;
  kind: FixtureLineKind;
  /** ms after the previous line should appear; first line uses the offset from t=0 */
  delayMs: number;
}

export interface RunWorkerFixture {
  capturedAt: string; // ISO date
  binaryVersion: string;
  /** Human-readable label for the badge: "Real ./run.sh — captured 2026-04-30" */
  badge: string;
  lines: FixtureLine[];
}

export const runWorkerFixture: RunWorkerFixture = {
  capturedAt: '2026-04-30',
  binaryVersion: 'v0.1.0',
  badge: 'Real ./run.sh — captured 2026-04-30',
  lines: [
    { text: '═══════════════════════════════════════════════════════', kind: 'header', delayMs: 0 },
    { text: '  Nasrudin Spontaneous Physics Discovery — domain=sr',     kind: 'header', delayMs: 80 },
    { text: '  No headline-result strategies. No headline axioms.',     kind: 'header', delayMs: 80 },
    { text: '  Pure combinatorics + GA over upstream postulates.',      kind: 'header', delayMs: 80 },
    { text: '═══════════════════════════════════════════════════════', kind: 'header', delayMs: 80 },
    // ── PASTE ~20 more verbatim lines from dist/captures/run-worker.log here ──
    // Each line is { text: '<exact line>', kind: <one-of>, delayMs: <int> }.
    // delayMs total should sum to ~10-12 seconds for a comfortable replay.
  ],
};
```

Replace the `// ── PASTE` placeholder with the real selected lines from the capture. Pick the `kind` per line:
- `header` for the banner block,
- `cmd` for `▶ ` lines (announcements),
- `ok` for `✓ ` lines (successes),
- `warn` for `! ` or `✗` lines (warnings/errors — likely none in a successful capture),
- `info` for `▶ API submission target:` and `worker_id:` lines,
- `output` for everything else (axiom names, generation rows, etc.).

`delayMs` per line: 60-150ms for fast lines (axiom names), 300-500ms for events that have wall-clock delays in reality (boot, generation completions). Sum should be ~10-12 seconds.

- [ ] **Step 11.3: Write `ga-viz.fixture.ts`**

```ts
// Real GA-cycle trace captured 2026-04-30. Source: dist/captures/ga-trace.log.
// Each row is verbatim from the worker's stdout.

export interface GaRow {
  /** GA operation: 'axiom' = seed; one of 'mutate' | 'crossover' | 'compose' otherwise. */
  op: 'axiom' | 'mutate' | 'crossover' | 'compose';
  expr: string;
  status: 'seed' | 'accepted' | 'rejected';
  /** Right-aligned annotation: "verified · 0.4s", "type mismatch", etc. */
  result: string;
}

export interface GaVizFixture {
  capturedAt: string;
  workerId: string;
  /** Generation index of the FIRST row below — subsequent rows share the same generation. */
  generationStart: number;
  rows: GaRow[];
}

export const gaVizFixture: GaVizFixture = {
  capturedAt: '2026-04-30',
  workerId: 'capture-2026-04-30',
  generationStart: 0, // ← replace with the actual generation number from the capture
  rows: [
    // ── PASTE 6-10 real rows here, each derived from a line in dist/captures/ga-trace.log ──
    // Example structure (replace with actual content):
    // { op: 'axiom',     expr: '…',        status: 'seed',     result: 'from postulate' },
    // { op: 'mutate',    expr: '…',        status: 'accepted', result: 'verified · 0.4s' },
    // { op: 'crossover', expr: '…',        status: 'accepted', result: 'verified · 1.1s' },
    // { op: 'mutate',    expr: '…',        status: 'rejected', result: 'type mismatch' },
  ],
};
```

Replace the `// ── PASTE` placeholder with 6-10 real rows derived from `dist/captures/ga-trace.log`. The `generationStart` comes from a line like `[gen 1·001]` in the capture (use the literal number that prefixes the chosen rows).

- [ ] **Step 11.4: Verify fixtures compile**

```bash
cd nasrudin-frontend && pnpm tsc --noEmit && cd ..
```

Expected: no TypeScript errors.

- [ ] **Step 11.5: Commit**

```bash
git add nasrudin-frontend/src/components/landing/run-worker.fixture.ts \
        nasrudin-frontend/src/components/landing/ga-viz.fixture.ts
git commit -m "frontend: typed fixtures from real worker capture"
```

### Task 12: Platform detection function — failing tests first

**Files:**
- Create: `nasrudin-frontend/src/components/landing/RunWorker.platform.test.ts`

- [ ] **Step 12.1: Write the failing tests**

```ts
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { detectPlatform, type Platform } from './RunWorker.platform';

function withNavigator(stub: Partial<Navigator>, fn: () => void) {
  const original = (globalThis as unknown as { navigator?: Navigator }).navigator;
  (globalThis as unknown as { navigator?: Navigator }).navigator =
    stub as Navigator;
  try {
    fn();
  } finally {
    (globalThis as unknown as { navigator?: Navigator }).navigator = original;
  }
}

describe('detectPlatform', () => {
  it('returns null when navigator is undefined (SSR)', () => {
    const original = (globalThis as unknown as { navigator?: Navigator }).navigator;
    (globalThis as unknown as { navigator?: Navigator }).navigator = undefined;
    try {
      expect(detectPlatform()).toBeNull();
    } finally {
      (globalThis as unknown as { navigator?: Navigator }).navigator = original;
    }
  });

  it('detects macOS Apple Silicon from a Safari UA', () => {
    withNavigator(
      {
        platform: 'MacIntel',
        userAgent:
          'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 Safari/605.1.15',
      },
      () => {
        // Apple Silicon Safari still reports `MacIntel` and `Intel Mac OS X`.
        // We default macOS to aarch64 because Apple-Silicon is the default since 2020.
        expect(detectPlatform()).toEqual<Platform>({ os: 'macos', arch: 'aarch64' });
      },
    );
  });

  it('detects macOS Intel when UA explicitly says Intel and we have no arm marker', () => {
    // We accept that detection cannot reliably distinguish — default macOS → aarch64.
    // This test pins the documented behaviour: macOS always returns aarch64 unless
    // we get an explicit arm64/aarch64 *negative* signal (which browsers don't emit).
    // Intel Mac users use the "Show all builds" disclosure to pick the x86_64 build.
    withNavigator(
      {
        platform: 'MacIntel',
        userAgent:
          'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 Chrome/120 Safari/537.36',
      },
      () => {
        expect(detectPlatform()).toEqual<Platform>({ os: 'macos', arch: 'aarch64' });
      },
    );
  });

  it('detects Windows x86_64 from Chrome UA', () => {
    withNavigator(
      {
        platform: 'Win32',
        userAgent:
          'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120 Safari/537.36',
      },
      () => {
        expect(detectPlatform()).toEqual<Platform>({ os: 'windows', arch: 'x86_64' });
      },
    );
  });

  it('detects Linux x86_64 from Firefox UA', () => {
    withNavigator(
      {
        platform: 'Linux x86_64',
        userAgent: 'Mozilla/5.0 (X11; Linux x86_64; rv:120.0) Gecko/20100101 Firefox/120.0',
      },
      () => {
        expect(detectPlatform()).toEqual<Platform>({ os: 'linux', arch: 'x86_64' });
      },
    );
  });

  it('detects Linux aarch64 from a Linux ARM UA', () => {
    withNavigator(
      {
        platform: 'Linux aarch64',
        userAgent: 'Mozilla/5.0 (X11; Linux aarch64; rv:120.0) Gecko/20100101 Firefox/120.0',
      },
      () => {
        expect(detectPlatform()).toEqual<Platform>({ os: 'linux', arch: 'aarch64' });
      },
    );
  });

  it('returns null for Android (not a supported worker target)', () => {
    withNavigator(
      {
        platform: 'Linux armv8l',
        userAgent:
          'Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 Chrome/120 Mobile Safari/537.36',
      },
      () => {
        expect(detectPlatform()).toBeNull();
      },
    );
  });
});
```

- [ ] **Step 12.2: Run the test, expect failure**

```bash
cd nasrudin-frontend && pnpm test --run src/components/landing/RunWorker.platform.test.ts
cd ..
```

Expected: FAIL with `Cannot find module './RunWorker.platform'`.

### Task 13: Implement platform detection

**Files:**
- Create: `nasrudin-frontend/src/components/landing/RunWorker.platform.ts`

- [ ] **Step 13.1: Write the implementation**

```ts
export type OsKind = 'macos' | 'linux' | 'windows';
export type ArchKind = 'x86_64' | 'aarch64';

export interface Platform {
  os: OsKind;
  arch: ArchKind;
}

/**
 * Best-effort platform detection from `navigator`. Returns `null` when
 * navigator is missing (SSR) or the platform is not a supported worker target.
 *
 * Notes:
 * - macOS: defaults to aarch64 (Apple Silicon has been the default since 2020).
 *   Browsers cannot reliably distinguish Intel from Apple Silicon — the Show
 *   All Builds disclosure on the page lets Intel users pick the x86_64 SKU.
 * - Linux: arch is derived from the literal UA string (X11; Linux <arch>).
 * - Windows: only x86_64 is shipped; UA is not used to gate detection.
 */
export function detectPlatform(): Platform | null {
  if (typeof navigator === 'undefined' || !navigator) return null;

  const ua = navigator.userAgent ?? '';
  const platform = navigator.platform ?? '';

  // Android masquerades as Linux on userAgent.platform — exclude it.
  if (/Android/i.test(ua)) return null;

  const isMac = /Mac/i.test(platform) || /Macintosh/i.test(ua);
  const isWin = /Win/i.test(platform) || /Windows/i.test(ua);
  const isLinux = /Linux/i.test(platform) && !isMac;

  if (isMac) return { os: 'macos', arch: 'aarch64' };
  if (isWin) return { os: 'windows', arch: 'x86_64' };
  if (isLinux) {
    const arm = /aarch64|arm64|armv8/i.test(`${platform} ${ua}`);
    return { os: 'linux', arch: arm ? 'aarch64' : 'x86_64' };
  }
  return null;
}
```

- [ ] **Step 13.2: Run the tests, expect pass**

```bash
cd nasrudin-frontend && pnpm test --run src/components/landing/RunWorker.platform.test.ts
cd ..
```

Expected: 7 passing tests.

- [ ] **Step 13.3: Commit**

```bash
git add nasrudin-frontend/src/components/landing/RunWorker.platform.ts \
        nasrudin-frontend/src/components/landing/RunWorker.platform.test.ts
git commit -m "frontend: detectPlatform() — pure unit-tested platform detection"
```

### Task 14: TerminalPreview component

**Files:**
- Create: `nasrudin-frontend/src/components/landing/TerminalPreview.tsx`

- [ ] **Step 14.1: Write the component**

```tsx
import { useEffect, useState } from 'react';
import type { RunWorkerFixture } from './run-worker.fixture';

interface Props {
  fixture: RunWorkerFixture;
}

const KIND_CLASS: Record<string, string> = {
  header: 'header',
  info: 'high',
  ok: 'ok',
  warn: 'no',
  cmd: 'high',
  output: 'out',
};

/**
 * Replays a captured worker session line-by-line. Loops once finished.
 * The "Real ./run.sh — captured YYYY-MM-DD" badge in the corner makes it
 * unambiguous that this is a recording, not a live feed.
 */
export function TerminalPreview({ fixture }: Props) {
  const { lines, badge } = fixture;
  const [shown, setShown] = useState(0);

  useEffect(() => {
    if (lines.length === 0) return;
    let cancelled = false;
    let timer: ReturnType<typeof setTimeout> | null = null;

    const advance = (idx: number) => {
      if (cancelled) return;
      if (idx >= lines.length) {
        // Loop after a 1.5s pause.
        timer = setTimeout(() => {
          if (!cancelled) {
            setShown(0);
            advance(0);
          }
        }, 1500);
        return;
      }
      setShown(idx + 1);
      const next = lines[idx + 1];
      timer = setTimeout(() => advance(idx + 1), next ? next.delayMs : 0);
    };

    timer = setTimeout(() => advance(0), lines[0]?.delayMs ?? 0);
    return () => {
      cancelled = true;
      if (timer) clearTimeout(timer);
    };
  }, [lines]);

  return (
    <div className="install-cli terminal-preview">
      <div className="install-cli-bar">
        <div className="cli-dot" />
        <div className="cli-dot" />
        <div className="cli-dot" />
        <span className="cli-title">~/nasrudin-worker · ./run.sh</span>
        <span className="cli-badge">{badge}</span>
      </div>
      <div className="install-cli-body">
        {lines.slice(0, shown).map((l, i) => (
          <div key={`${i}-${l.text}`} className={`term-line ${KIND_CLASS[l.kind] ?? ''}`}>
            {l.text}
          </div>
        ))}
        {shown < lines.length && <span className="cursor" />}
      </div>
    </div>
  );
}
```

- [ ] **Step 14.2: Compile-check**

```bash
cd nasrudin-frontend && pnpm tsc --noEmit && cd ..
```

Expected: no errors.

- [ ] **Step 14.3: Commit**

```bash
git add nasrudin-frontend/src/components/landing/TerminalPreview.tsx
git commit -m "frontend: TerminalPreview replays captured worker output"
```

### Task 15: RunWorker component

**Files:**
- Create: `nasrudin-frontend/src/components/landing/RunWorker.tsx`

- [ ] **Step 15.1: Write the component**

```tsx
import { useMemo, useState } from 'react';
import { Link } from '@tanstack/react-router';
import { detectPlatform, type ArchKind, type OsKind } from './RunWorker.platform';
import { TerminalPreview } from './TerminalPreview';
import { runWorkerFixture } from './run-worker.fixture';

const RELEASE_BASE = 'https://github.com/Nasdin/nasrudin/releases/latest/download';

interface Build {
  os: OsKind;
  arch: ArchKind;
  ext: 'tar.gz' | 'zip';
  label: string;        // "macOS · Apple Silicon"
  archLabel: string;    // "aarch64-apple-darwin"
}

const BUILDS: Build[] = [
  { os: 'macos',   arch: 'aarch64', ext: 'tar.gz', label: 'macOS · Apple Silicon', archLabel: 'aarch64-apple-darwin' },
  { os: 'macos',   arch: 'x86_64',  ext: 'tar.gz', label: 'macOS · Intel',          archLabel: 'x86_64-apple-darwin' },
  { os: 'linux',   arch: 'x86_64',  ext: 'tar.gz', label: 'Linux · x86_64',         archLabel: 'x86_64-unknown-linux-gnu' },
  { os: 'linux',   arch: 'aarch64', ext: 'tar.gz', label: 'Linux · aarch64',        archLabel: 'aarch64-unknown-linux-gnu' },
  { os: 'windows', arch: 'x86_64',  ext: 'zip',    label: 'Windows · x86_64',       archLabel: 'x86_64-pc-windows-gnu' },
];

const ELAN_UNIX = 'curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y';
const ELAN_WIN  = 'iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex';

function bundleName(b: Build): string {
  return `nasrudin-worker-${b.os}-${b.arch}`;
}
function downloadUrl(b: Build): string {
  return `${RELEASE_BASE}/${bundleName(b)}.${b.ext}`;
}
function shaUrl(b: Build): string {
  return `${downloadUrl(b)}.sha256`;
}
function extractRunUnix(b: Build): string {
  return `tar xzf ${bundleName(b)}.tar.gz
cd ${bundleName(b)}
NASRUDIN_WORKER_KEY=nsk_worker_… ./run.sh`;
}
const EXTRACT_RUN_WIN = `Expand-Archive nasrudin-worker-windows-x86_64.zip
cd nasrudin-worker-windows-x86_64
$env:NASRUDIN_WORKER_KEY="nsk_worker_…"; .\\run.ps1`;

function CopyButton({ text }: { text: string }) {
  const [copied, setCopied] = useState(false);
  return (
    <button
      type="button"
      className="copy-btn"
      onClick={async () => {
        try {
          await navigator.clipboard.writeText(text);
          setCopied(true);
          setTimeout(() => setCopied(false), 1400);
        } catch {
          // clipboard blocked — silently no-op
        }
      }}
    >
      {copied ? 'copied' : 'copy'}
    </button>
  );
}

function CodeBlock({ children }: { children: string }) {
  return (
    <div className="code-block-wrap">
      <pre className="code-block">{children}</pre>
      <CopyButton text={children} />
    </div>
  );
}

function PrimaryCard({ build, detected }: { build: Build; detected: boolean }) {
  return (
    <div className={`run-worker-card ${detected ? 'detected' : ''}`}>
      {detected && <div className="run-worker-card-badge">detected</div>}
      <div className="run-worker-card-os">{build.label}</div>
      <a className="btn btn-primary run-worker-card-btn" href={downloadUrl(build)}>
        Download .{build.ext}
      </a>
      <a className="run-worker-card-sha" href={shaUrl(build)}>
        sha256 ↗
      </a>
    </div>
  );
}

export function RunWorker() {
  const detected = useMemo(() => detectPlatform(), []);
  const [showAll, setShowAll] = useState(false);
  const [runTab, setRunTab] = useState<'unix' | 'win'>('unix');
  const [leanTab, setLeanTab] = useState<'unix' | 'win'>('unix');

  // The three primary cards: macOS (the detected arch, or Apple Silicon if undetected),
  // Linux x86_64 (most common), Windows x86_64.
  const macBuild = BUILDS.find(
    (b) => b.os === 'macos' && b.arch === (detected?.os === 'macos' ? detected.arch : 'aarch64'),
  )!;
  const linuxBuild = BUILDS.find(
    (b) =>
      b.os === 'linux' && b.arch === (detected?.os === 'linux' ? detected.arch : 'x86_64'),
  )!;
  const winBuild = BUILDS.find((b) => b.os === 'windows')!;

  // The build the user's platform points at — for the Step 4 extract command.
  const myBuild = detected
    ? (BUILDS.find((b) => b.os === detected.os && b.arch === detected.arch) ?? macBuild)
    : macBuild;

  return (
    <div className="run-worker">
      <div className="run-worker-main">
        <ol className="run-worker-steps">
          <li className="run-worker-step">
            <div className="run-worker-step-num">1</div>
            <div className="run-worker-step-body">
              <h3>Get a worker key</h3>
              <p>
                Sign in, then open <Link to="/api-keys">/api-keys</Link> → "+ New key" → Kind:{' '}
                <em>Worker</em>. Save the <code>nsk_worker_…</code> value.
              </p>
              <Link to="/api-keys" className="btn btn-secondary">
                Open /api-keys →
              </Link>
            </div>
          </li>

          <li className="run-worker-step">
            <div className="run-worker-step-num">2</div>
            <div className="run-worker-step-body">
              <h3>Install the Lean toolchain (one-time, ~200 MB)</h3>
              <div className="lead-tabs run-worker-tabs">
                <button
                  type="button"
                  className={`lead-tab ${leanTab === 'unix' ? 'active' : ''}`}
                  onClick={() => setLeanTab('unix')}
                >
                  macOS / Linux
                </button>
                <button
                  type="button"
                  className={`lead-tab ${leanTab === 'win' ? 'active' : ''}`}
                  onClick={() => setLeanTab('win')}
                >
                  Windows (PowerShell)
                </button>
              </div>
              <CodeBlock>{leanTab === 'unix' ? ELAN_UNIX : ELAN_WIN}</CodeBlock>
            </div>
          </li>

          <li className="run-worker-step">
            <div className="run-worker-step-num">3</div>
            <div className="run-worker-step-body">
              <h3>Download for your platform</h3>
              <div className="run-worker-cards">
                <PrimaryCard build={macBuild} detected={detected?.os === 'macos'} />
                <PrimaryCard build={linuxBuild} detected={detected?.os === 'linux'} />
                <PrimaryCard build={winBuild} detected={detected?.os === 'windows'} />
              </div>
              <button
                type="button"
                className="run-worker-disclosure"
                onClick={() => setShowAll((v) => !v)}
              >
                {showAll ? '▾' : '▸'} Show all builds ({BUILDS.length})
              </button>
              {showAll && (
                <ul className="run-worker-all-builds">
                  {BUILDS.map((b) => (
                    <li key={`${b.os}-${b.arch}`}>
                      <span className="run-worker-build-label">{b.label}</span>
                      <span className="run-worker-build-arch">({b.archLabel})</span>
                      <a href={downloadUrl(b)}>.{b.ext}</a>
                      <a href={shaUrl(b)}>sha256</a>
                    </li>
                  ))}
                </ul>
              )}
            </div>
          </li>
        </ol>

        <div className="run-worker-preview">
          <div className="overline">Live preview · what you'll see when it runs</div>
          <TerminalPreview fixture={runWorkerFixture} />
        </div>

        <ol className="run-worker-steps" start={4}>
          <li className="run-worker-step">
            <div className="run-worker-step-num">4</div>
            <div className="run-worker-step-body">
              <h3>Extract and run</h3>
              <div className="lead-tabs run-worker-tabs">
                <button
                  type="button"
                  className={`lead-tab ${runTab === 'unix' ? 'active' : ''}`}
                  onClick={() => setRunTab('unix')}
                >
                  macOS / Linux
                </button>
                <button
                  type="button"
                  className={`lead-tab ${runTab === 'win' ? 'active' : ''}`}
                  onClick={() => setRunTab('win')}
                >
                  Windows (PowerShell)
                </button>
              </div>
              <CodeBlock>
                {runTab === 'unix' ? extractRunUnix(myBuild) : EXTRACT_RUN_WIN}
              </CodeBlock>
              <p className="margin-note" style={{ marginTop: 12 }}>
                First run warms the Mathlib cache (a few minutes); next runs reuse it.
                Ctrl+C is clean.
              </p>
            </div>
          </li>
        </ol>
      </div>

      <aside className="install-side run-worker-aside">
        <h3 className="h3" style={{ marginBottom: 8, fontSize: 24 }}>
          What you'll need
        </h3>
        <p style={{ marginBottom: 24, color: 'var(--ink-500)' }}>
          A modest desktop or cloud VM is enough. The harder you push, the faster physics
          arrives.
        </p>
        <ol className="install-reqs">
          <li>
            <span className="install-req-num">i.</span>
            <span className="install-req-name">
              CPU
              <span>4 cores minimum, 16+ recommended for serious throughput.</span>
            </span>
            <span className="install-req-val">x86_64 / arm64</span>
          </li>
          <li>
            <span className="install-req-num">ii.</span>
            <span className="install-req-name">
              Memory
              <span>Lean 4 likes RAM. The Mathlib snapshot wants room.</span>
            </span>
            <span className="install-req-val">≥ 8 GB</span>
          </li>
          <li>
            <span className="install-req-num">iii.</span>
            <span className="install-req-name">
              Disk
              <span>Local Mathlib cache + prover state.</span>
            </span>
            <span className="install-req-val">≥ 20 GB</span>
          </li>
          <li>
            <span className="install-req-num">iv.</span>
            <span className="install-req-name">
              Network
              <span>Workers POST verified theorems to the central server.</span>
            </span>
            <span className="install-req-val">~5 MB/h</span>
          </li>
          <li>
            <span className="install-req-num">v.</span>
            <span className="install-req-name">
              Patience
              <span>Most candidates are nonsense. The wise fool knew this.</span>
            </span>
            <span className="install-req-val">∞</span>
          </li>
        </ol>
      </aside>
    </div>
  );
}
```

- [ ] **Step 15.2: Compile-check**

```bash
cd nasrudin-frontend && pnpm tsc --noEmit && cd ..
```

Expected: no errors.

- [ ] **Step 15.3: Commit**

```bash
git add nasrudin-frontend/src/components/landing/RunWorker.tsx
git commit -m "frontend: RunWorker section — real download UX, replaces InstallNode"
```

### Task 16: Add CSS for the new section

**Files:**
- Modify: `nasrudin-frontend/src/styles/styles.css`

- [ ] **Step 16.1: Append RunWorker styles**

Append to the end of `styles.css`:

```css
/* ─── RunWorker section ─────────────────────────────────────────────────── */

.run-worker {
  display: grid;
  grid-template-columns: 1fr 320px;
  gap: 48px;
  align-items: start;
}

@media (max-width: 960px) {
  .run-worker { grid-template-columns: 1fr; }
}

.run-worker-steps {
  list-style: none;
  padding: 0;
  margin: 0 0 32px 0;
  display: grid;
  gap: 32px;
}

.run-worker-step {
  display: grid;
  grid-template-columns: 56px 1fr;
  gap: 24px;
  align-items: start;
}

.run-worker-step-num {
  width: 40px;
  height: 40px;
  border-radius: 50%;
  background: var(--terracotta-300);
  color: var(--paper-50);
  font-family: var(--font-serif);
  font-size: 22px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.run-worker-step-body h3 {
  font-family: var(--font-serif);
  font-size: 22px;
  margin: 4px 0 12px 0;
}

.run-worker-tabs { margin-bottom: 12px; }

.run-worker-cards {
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: 16px;
  margin: 16px 0;
}

@media (max-width: 720px) {
  .run-worker-cards { grid-template-columns: 1fr; }
}

.run-worker-card {
  border: 1px solid var(--paper-300);
  border-radius: 12px;
  padding: 20px;
  background: var(--paper-50);
  position: relative;
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.run-worker-card.detected {
  border-color: var(--terracotta-300);
  box-shadow: 0 0 0 2px var(--terracotta-50);
}

.run-worker-card-badge {
  position: absolute;
  top: -10px;
  right: 16px;
  background: var(--terracotta-300);
  color: var(--paper-50);
  font-size: 11px;
  letter-spacing: var(--tracking-allcaps);
  text-transform: uppercase;
  padding: 2px 8px;
  border-radius: 999px;
}

.run-worker-card-os {
  font-family: var(--font-serif);
  font-size: 18px;
}

.run-worker-card-btn { width: 100%; text-align: center; }

.run-worker-card-sha {
  color: var(--ink-500);
  font-family: var(--font-mono);
  font-size: 12px;
  text-align: center;
}

.run-worker-disclosure {
  background: none;
  border: none;
  color: var(--terracotta-700);
  font-family: var(--font-mono);
  font-size: 13px;
  padding: 8px 0;
  cursor: pointer;
}

.run-worker-all-builds {
  list-style: none;
  padding: 12px 0 0 0;
  margin: 0;
  border-top: 1px dashed var(--paper-300);
}

.run-worker-all-builds li {
  display: grid;
  grid-template-columns: 1fr auto auto auto;
  gap: 16px;
  padding: 8px 0;
  font-family: var(--font-mono);
  font-size: 13px;
  align-items: center;
}

.run-worker-build-arch { color: var(--ink-500); font-size: 12px; }

.run-worker-preview { margin: 32px 0; }

.run-worker-aside { position: sticky; top: 24px; }

@media (max-width: 960px) {
  .run-worker-aside { position: static; }
}

/* ─── TerminalPreview tweaks (reuses .install-cli) ────────────────────── */

.terminal-preview .cli-badge {
  margin-left: auto;
  font-family: var(--font-mono);
  font-size: 11px;
  color: var(--ink-500);
  text-transform: uppercase;
  letter-spacing: var(--tracking-allcaps);
}

.term-line.header { color: var(--terracotta-300); }
.term-line.high   { color: var(--saffron-300); }
.term-line.ok     { color: var(--olive-500); }
.term-line.no     { color: var(--terracotta-700); }
.term-line.out    { color: var(--ink-500); }

/* ─── CopyButton ───────────────────────────────────────────────────────── */

.code-block-wrap { position: relative; }

.copy-btn {
  position: absolute;
  top: 8px;
  right: 8px;
  background: var(--paper-50);
  border: 1px solid var(--paper-300);
  border-radius: 6px;
  padding: 4px 10px;
  font-family: var(--font-mono);
  font-size: 11px;
  color: var(--ink-700);
  cursor: pointer;
}

.copy-btn:hover { background: var(--paper-100); }
```

- [ ] **Step 16.2: Verify the dev server still builds**

```bash
cd nasrudin-frontend && pnpm build 2>&1 | tail -10 && cd ..
```

Expected: build completes without CSS warnings.

- [ ] **Step 16.3: Commit**

```bash
git add nasrudin-frontend/src/styles/styles.css
git commit -m "frontend: styles for RunWorker download cards + terminal preview"
```

---

## Phase 6 — Frontend de-mock

### Task 17: Rewrite GAViz to consume the captured fixture

**Files:**
- Modify: `nasrudin-frontend/src/components/landing/GAViz.tsx` (replace entire body)

- [ ] **Step 17.1: Rewrite the file**

Replace the contents of `GAViz.tsx` with:

```tsx
import { useEffect, useState } from 'react';
import { gaVizFixture } from './ga-viz.fixture';

export function GAViz() {
  const { rows, workerId, generationStart } = gaVizFixture;
  const [gen, setGen] = useState(0);

  useEffect(() => {
    if (rows.length === 0) return;
    const t = setInterval(() => setGen((g) => (g + 1) % rows.length), 1400);
    return () => clearInterval(t);
  }, [rows.length]);

  return (
    <div className="ga-viz">
      <div
        style={{
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'baseline',
          marginBottom: 20,
        }}
      >
        <div>
          <div className="overline" style={{ marginBottom: 6 }}>
            Generation {generationStart.toLocaleString()} · captured trace
          </div>
          <div
            style={{
              fontFamily: 'var(--font-serif)',
              fontSize: 22,
              fontStyle: 'italic',
              color: 'var(--ink-700)',
            }}
          >
            Real GA cycle from a worker run on {gaVizFixture.capturedAt}.
          </div>
        </div>
        <div style={{ fontFamily: 'var(--font-mono)', fontSize: 12, color: 'var(--ink-500)' }}>
          worker · {workerId}
        </div>
      </div>
      <div className="ga-rows">
        {rows.map((row, i) => {
          const visible = i <= gen;
          const cls =
            row.status === 'accepted' ? 'accepted' : row.status === 'rejected' ? 'rejected' : '';
          return (
            <div
              className={`ga-row ${cls}`}
              key={`${row.op}-${row.expr}`}
              style={{
                opacity: visible ? (cls === 'rejected' ? 0.45 : 1) : 0.18,
                transition: 'opacity .6s',
              }}
            >
              <span className="ga-op">{row.op}</span>
              <span className="ga-expr">{row.expr}</span>
              <span
                className={`ga-result ${
                  row.status === 'accepted' ? 'ok' : row.status === 'rejected' ? 'no' : ''
                }`}
              >
                {row.result}
              </span>
            </div>
          );
        })}
      </div>
    </div>
  );
}
```

- [ ] **Step 17.2: Verify no `GA_GENERATIONS` literal remains anywhere**

```bash
grep -rn "GA_GENERATIONS" nasrudin-frontend/src
```

Expected: empty output.

- [ ] **Step 17.3: Compile-check**

```bash
cd nasrudin-frontend && pnpm tsc --noEmit && cd ..
```

Expected: no errors.

- [ ] **Step 17.4: Commit**

```bash
git add nasrudin-frontend/src/components/landing/GAViz.tsx
git commit -m "frontend: GAViz reads captured fixture, no more hardcoded GA_GENERATIONS"
```

### Task 18: Strip FALLBACK_TICKER + FALLBACK_HERO from HeroLiveTheorem

**Files:**
- Modify: `nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx`

- [ ] **Step 18.1: Rewrite the file**

Replace the contents with:

```tsx
import { useEffect, useState, useMemo } from 'react';
import { Link } from '@tanstack/react-router';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import { useRecentTheorems } from '~/lib/queries';

function getTimeAgo(date: Date): string {
  const seconds = Math.floor((Date.now() - date.getTime()) / 1000);
  if (seconds < 60) return 'just now';
  const minutes = Math.floor(seconds / 60);
  if (minutes < 60) return `${minutes}m ago`;
  const hours = Math.floor(minutes / 60);
  if (hours < 24) return `${hours}h ago`;
  const days = Math.floor(hours / 24);
  return `${days}d ago`;
}

/** Render a real recent theorem as a "VERIFIED  thm:<id>  <statement>" ticker line. */
function tickerLineFor(t: { id: Uint8Array | number[]; latex?: string | null; canonical_statement?: string | null }): string {
  const id = bytesToHex(t.id).slice(0, 6);
  const stmt = (t.latex ?? t.canonical_statement ?? '').toString().slice(0, 80);
  return `VERIFIED  thm:${id}…  ${stmt}`;
}

export function HeroLiveTheorem() {
  const recent = useRecentTheorems(12);
  const [idx, setIdx] = useState(0);
  const [tickerLines, setTickerLines] = useState<string[]>([]);
  const [tickIdx, setTickIdx] = useState(0);

  // Shuffle theorems on load to avoid same order every time.
  const shuffledTheorems = useMemo(() => {
    if (!recent.data?.theorems) return [];
    const arr = [...recent.data.theorems];
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      const temp = arr[i];
      if (arr[j] !== undefined) arr[i] = arr[j];
      if (temp !== undefined) arr[j] = temp;
    }
    return arr;
  }, [recent.data?.theorems]);

  // Seed the ticker with REAL recent theorems as soon as the REST query lands.
  useEffect(() => {
    if (recent.data?.theorems?.length) {
      setTickerLines(
        recent.data.theorems.slice(0, 8).map(tickerLineFor),
      );
    }
  }, [recent.data]);

  const total = shuffledTheorems.length;
  useEffect(() => {
    if (total === 0) return;
    const t = setInterval(() => setIdx((i) => (i + 1) % total), 5500);
    return () => clearInterval(t);
  }, [total]);

  // SSE subscription to /api/events/discoveries — prepends each verified theorem.
  useEffect(() => {
    if (typeof window === 'undefined') return;
    let failures = 0;
    const url = `${import.meta.env.VITE_API_URL ?? 'http://localhost:3001'}/api/events/discoveries`;
    let es: EventSource | null;
    try {
      es = new EventSource(url, { withCredentials: true });
    } catch {
      return;
    }
    es.onmessage = (ev) => {
      const t = (() => {
        try { return JSON.parse(ev.data); } catch { return null; }
      })();
      if (t && typeof t === 'object' && 'theorem_id' in t) {
        const ti = t as { theorem_id: string };
        setTickerLines((prev) =>
          [`VERIFIED  thm:${ti.theorem_id.slice(0, 6)}…`, ...prev].slice(0, 12),
        );
      }
    };
    es.onerror = () => {
      failures += 1;
      if (failures >= 3) es?.close();
    };
    return () => es?.close();
  }, []);

  useEffect(() => {
    if (tickerLines.length === 0) return;
    const t = setInterval(() => setTickIdx((i) => (i + 1) % tickerLines.length), 1800);
    return () => clearInterval(t);
  }, [tickerLines.length]);

  const t = shuffledTheorems[idx];
  const stmt = t?.latex ?? t?.canonical_statement;
  const id = t ? bytesToHex(t.id) : null;
  const domain = t?.domain;
  const generation = t?.generation;
  const verifiedAt = t?.verified_at ? new Date(t.verified_at) : null;
  const timeAgo = verifiedAt ? getTimeAgo(verifiedAt) : null;

  // No real theorem yet → skeleton card. Never invent one.
  if (!t || !id || !stmt) {
    return (
      <div>
        <div className="theorem-card theorem-card-loading" aria-live="polite">
          <div className="theorem-card-head">
            <span className="theorem-card-id" style={{ opacity: 0.4 }}>thm:…</span>
            <span className="verified-badge">
              <span className="verified-dot" /> waiting for live events…
            </span>
          </div>
          <div className="theorem-card-body">
            <div className="theorem-statement" style={{ opacity: 0.4 }}>—</div>
            <div className="theorem-tag" style={{ opacity: 0.4 }}>connecting…</div>
          </div>
        </div>
        <div className="ticker">
          <span className="ticker-label">Live</span>
          <span className="ticker-text" style={{ color: 'var(--ink-500)' }}>
            waiting for live events…
          </span>
        </div>
      </div>
    );
  }

  return (
    <div>
      <Link to="/theorem/$id" params={{ id }} className="theorem-card-link">
        <div className="theorem-card">
          <div className="theorem-card-head">
            <span className="theorem-card-id">{id.slice(0, 8)}</span>
            <span className="verified-badge">
              <span className="verified-dot" /> Verified · Lean 4
            </span>
          </div>
          <div className="theorem-card-body">
            <div className="theorem-statement">
              <MathExpr source={stmt} block />
            </div>
            <div className="theorem-name">{id}</div>
            <div className="theorem-tag">
              {domain} · gen {generation}
              {timeAgo && <span> · {timeAgo}</span>}
            </div>
          </div>
        </div>
      </Link>
      <div className="ticker">
        <span className="ticker-label">Live</span>
        <span className="ticker-text" key={tickIdx}>
          <span className={tickerLines[tickIdx]?.startsWith('VERIFIED') ? 'ok' : 'reject'}>
            {tickerLines[tickIdx] ?? 'waiting for live events…'}
          </span>
        </span>
      </div>
    </div>
  );
}
```

- [ ] **Step 18.2: Verify the literals are gone from the codebase**

```bash
grep -rn "FALLBACK_TICKER\|FALLBACK_HERO\|Schwarz inequality" nasrudin-frontend/src
```

Expected: empty output.

- [ ] **Step 18.3: Compile-check**

```bash
cd nasrudin-frontend && pnpm tsc --noEmit && cd ..
```

Expected: no errors.

- [ ] **Step 18.4: Commit**

```bash
git add nasrudin-frontend/src/components/landing/HeroLiveTheorem.tsx
git commit -m "frontend: HeroLiveTheorem — real ticker only, no FALLBACK_TICKER/FALLBACK_HERO"
```

### Task 19: Wire RunWorker into the landing page; delete InstallNode

**Files:**
- Modify: `nasrudin-frontend/src/routes/index.tsx`
- Delete: `nasrudin-frontend/src/components/landing/InstallNode.tsx`

- [ ] **Step 19.1: Update the landing route**

In `nasrudin-frontend/src/routes/index.tsx`:

a. Replace this import line:

```tsx
import { InstallNode } from '~/components/landing/InstallNode';
```

with:

```tsx
import { RunWorker } from '~/components/landing/RunWorker';
```

b. Replace this lede line at §06:

```
                Three commands — install, register, run. Your machine starts mutating axioms in
                seconds. Every theorem your node verifies and the server accepts gets your pseudonym
                attached, forever.
```

with:

```
                Four steps — key, Lean, download, run. Your machine starts mutating axioms in
                minutes. Every theorem your node verifies and the server accepts gets your pseudonym
                attached, forever.
```

c. Replace this render line:

```tsx
          <InstallNode />
```

with:

```tsx
          <RunWorker />
```

- [ ] **Step 19.2: Delete the old component**

```bash
git rm nasrudin-frontend/src/components/landing/InstallNode.tsx
```

- [ ] **Step 19.3: Compile + lint**

```bash
cd nasrudin-frontend && pnpm check 2>&1 | tail -20 && cd ..
```

Expected: zero errors. If biome complains about the appended CSS or any unused imports, fix inline.

- [ ] **Step 19.4: Commit**

```bash
git add nasrudin-frontend/src/routes/index.tsx
git commit -m "frontend: landing wires RunWorker + drops InstallNode"
```

---

## Phase 7 — Audit + manual verification

### Task 20: Audit remaining landing components for invented data

**Files:** read-only audit; only modify if a fake is found.

- [ ] **Step 20.1: Re-grep for fake-data patterns**

```bash
grep -rEn "FALLBACK|MOCK|FAKE|hardcoded|sample[A-Z]|placeholder|home-pc-|nasrudin\.dev" \
    nasrudin-frontend/src
```

For each match: is it in a fixture (acceptable — `*.fixture.ts` files are real captured data), a test file (acceptable), or a component (NOT acceptable for the landing). Component matches must be fixed in this task.

- [ ] **Step 20.2: Verify `TheoremBrowser`, `PipelineDiagram`, `WorkerMap`, `RediscoveryGrid` use live data**

```bash
grep -nE "useStats|useWorkers|useRecentTheorems|useFeaturedDiscoveries|useQuery" \
  nasrudin-frontend/src/components/landing/*.tsx
```

Expected: each landing component (other than the captured-fixture-driven `GAViz` and `RunWorker`) sources its data from a `use…` query hook. If any component contains literal arrays of theorem rows or hardcoded stats, fix it in this task.

- [ ] **Step 20.3: If anything was modified, commit**

```bash
git status --short nasrudin-frontend/src/components/landing/
# Only commit if there are actual changes:
git add nasrudin-frontend/src/components/landing/
git commit -m "frontend: replace remaining mocked landing data with live queries" || true
```

### Task 21: Visual smoke test in the dev server

**Files:** none — runtime check.

- [ ] **Step 21.1: Start the dev stack**

In one terminal:

```bash
just up
```

Wait for `[web]` lines to indicate Vite is serving on `localhost:3000`.

- [ ] **Step 21.2: Open the landing page and verify**

Open <http://localhost:3000>. Confirm:

a. Hero `HeroLiveTheorem` shows a real recent theorem (or the "waiting for live events…" skeleton if the local API has none). It should NOT show the Schwarz inequality or any `thm:9f3a2c` invented IDs.

b. §02 `GAViz` shows `Generation N · captured trace` (with N matching `gaVizFixture.generationStart`) and the worker label `worker · capture-2026-04-30`. The rows should match the fixture content.

c. §06 `RunWorker` shows:
   - Step 1 with the /api-keys CTA,
   - Step 2 with the elan tabs,
   - Step 3 with three primary cards — your platform's card has the "(detected)" badge,
   - The "Show all builds (5)" disclosure expands to all 5 SKUs,
   - The TerminalPreview animates real captured lines (badge in the corner reads "Real ./run.sh — captured 2026-04-30"),
   - Step 4 with the run-command tabs.

d. Click a download button. The browser should attempt to navigate to `https://github.com/Nasdin/nasrudin/releases/latest/download/nasrudin-worker-…`. Right now this 404s (no release yet) — that's expected. Confirm the URL is right.

e. Click the disclosure, click each `.sha256` link. Should navigate to `…/nasrudin-worker-….sha256`.

f. Tab between macOS/Linux and Windows in Steps 2 and 4. Copy buttons populate the clipboard.

If anything is wrong, fix it in `RunWorker.tsx` / `RunWorker.platform.ts` / `styles.css` and re-run this step.

- [ ] **Step 21.3: Stop the dev stack**

Ctrl+C the `just up` terminal.

### Task 22: Run all tests and lint before cutting the release

**Files:** none — gate.

- [ ] **Step 22.1: Frontend tests + lint**

```bash
cd nasrudin-frontend
pnpm test --run
pnpm check
cd ..
```

Expected: all tests pass; biome reports no errors; tsc reports no errors.

- [ ] **Step 22.2: Engine clippy + fmt**

```bash
just check-engine
```

Expected: zero warnings (clippy is `-D warnings`).

- [ ] **Step 22.3: Verify clean tree**

```bash
git status --porcelain
```

Expected: empty output.

---

## Phase 8 — Cut the release

### Task 23: Cut `worker-v0.1.0`

**Files:** none modified by you — the recipe handles tag + push + upload.

- [ ] **Step 23.1: Verify `gh` is authenticated and has write access**

```bash
gh auth status
gh repo view Nasdin/nasrudin --json viewerPermission
```

Expected: `viewerPermission` is `ADMIN` or `MAINTAIN` or `WRITE`.

- [ ] **Step 23.2: Cut the release**

```bash
just release-worker v0.1.0
```

Walk through the recipe interactively:

a. Validates the `vX.Y.Z` shape — passes.
b. Confirms clean tree — passes (release work has all been committed).
c. Generates AI release notes from `git log` since the previous worker tag (none exists; uses full history).
d. Prints the notes and asks for confirmation. **Read the notes**. If they're sane (mentions the new release pipeline + landing page work), type `y` and Enter.
e. Builds all 5 bundles via `just build-worker-all` (~2-5 min on Apple Silicon).
f. Tags `worker-v0.1.0`, pushes the tag.
g. Calls `gh release create` to publish the release with all 10 assets (5 archives + 5 sha256s).

- [ ] **Step 23.3: Verify the release exists and assets are downloadable**

```bash
gh release view worker-v0.1.0 --repo Nasdin/nasrudin
gh release view worker-v0.1.0 --repo Nasdin/nasrudin --json assets --jq '.assets[].name'
```

Expected: 10 asset names listed (5 archives + 5 sha256 sidecars).

- [ ] **Step 23.4: Verify `releases/latest/download/…` redirects resolve**

```bash
for sku in linux-x86_64 linux-aarch64 darwin-x86_64 darwin-arm64; do
  echo -n "$sku.tar.gz: "
  curl -sI "https://github.com/Nasdin/nasrudin/releases/latest/download/nasrudin-worker-${sku}.tar.gz" \
    | grep -iE "^(HTTP|location)" | head -2
done
echo -n "windows-x86_64.zip: "
curl -sI "https://github.com/Nasdin/nasrudin/releases/latest/download/nasrudin-worker-windows-x86_64.zip" \
  | grep -iE "^(HTTP|location)" | head -2
```

Expected: each request returns `HTTP/2 302` (or `HTTP/1.1 302`) with a `location:` redirect to the actual asset URL containing `worker-v0.1.0`.

### Task 24: End-to-end verification on a clean machine path

**Files:** none — runtime smoke.

- [ ] **Step 24.1: Smoke-run from the published release on this Mac**

```bash
cd /tmp && rm -rf nasrudin-smoke && mkdir nasrudin-smoke && cd nasrudin-smoke
curl -L https://github.com/Nasdin/nasrudin/releases/latest/download/nasrudin-worker-darwin-arm64.tar.gz \
  -o bundle.tar.gz
shasum -a 256 bundle.tar.gz
curl -sL https://github.com/Nasdin/nasrudin/releases/latest/download/nasrudin-worker-darwin-arm64.tar.gz.sha256
# The two sha256 values should match.

tar xzf bundle.tar.gz
cd nasrudin-worker-darwin-arm64

NASRUDIN_API_URL=https://api.nasrudin.org \
NASRUDIN_WORKER_KEY="$(cat ~/.nasrudin-worker-key)" \
NASRUDIN_WORKER_ID=smoke-2026-04-30 \
./run.sh --gens 3 --pop 16 --max-lake 2
```

Expected: identical end-to-end behaviour to Task 7 — banner, API target, axiom store, elaborator boot, GA generations, clean exit. The published binary works.

```bash
cd ~ && rm -rf /tmp/nasrudin-smoke
```

- [ ] **Step 24.2: Verify the live landing page now points to the real release**

Open <https://nasrudin.org> (or wherever the production frontend is deployed). The §06 RunWorker section's download buttons should now resolve to actual `worker-v0.1.0` assets, not 404. The auto-detected platform card should highlight with the (detected) badge.

> If the production frontend hasn't been deployed since the landing changes, deploy it now via `just deploy ip=<droplet-ip>`. (This is a separate operation; the spec covers the worker-release flow specifically. If a frontend deploy is out of scope today, log a TODO to deploy it; the release is not blocked by it.)

---

## Phase 9 — Restore in-flight work

### Task 25: Pop the stash

**Files:** restoring whatever was in the stash from Task 0.

- [ ] **Step 25.1: List stashes to confirm what's coming back**

```bash
git stash list
```

Expected: `stash@{0}` is `pre-worker-release-WIP`.

- [ ] **Step 25.2: Pop**

```bash
git stash pop
git status --short
```

Expected: the same uncommitted file list that was present before Task 0 (about 30 files).

> If the stash pop reports a conflict, that means one of your release commits touched the same file as an in-flight change. Resolve manually — the release commits are intentional, the stashed change should be reapplied where compatible.

---

## Self-review — coverage map (spec §x → task)

| Spec section | Implemented by |
|---|---|
| §1 Scope (1) build pipeline | Tasks 3-6 |
| §1 Scope (2) public-readiness | Tasks 1-2 |
| §1 Scope (3) landing de-mock | Tasks 7-9, 11, 14-19 |
| §2 C1 No GH Actions | Task 6.2 (delete workflow) |
| §2 C2 zigbuild toolchain | Tasks 3, 4 |
| §2 C3 glibc 2.17 pin | Task 5 (recipe), Task 4 (helper) |
| §2 C4 Windows MinGW | Task 5 (recipe target spec) |
| §2 C5 5-target matrix | Task 5 |
| §2 C6 worker-v0.1.0 | Task 23 |
| §2 C7 AGPL-3.0 | Tasks 1-2 |
| §2 C8 No fakes | Tasks 8-9, 11, 17-20 |
| §2 C9 Stash WIP | Tasks 0, 25 |
| §3.1 Build pipeline | Tasks 4-6 |
| §3.2 Landing flow | Tasks 17-19 |
| §4.1 Justfile changes | Tasks 5-6 |
| §4.2 LICENSE + license metadata | Tasks 1-2 |
| §4.3 RunWorker component | Tasks 12-15 |
| §4.4 GAViz rewrite | Task 17 |
| §4.5 HeroLiveTheorem fallback removal | Task 18 |
| §4.6 Other-component audit | Task 20 |
| §5 Data flow | Tasks 5-6, 15 |
| §6 Error handling + edge cases | Task 12 (SSR null), Task 18 (skeleton), Task 22 (gates) |
| §7 Testing | Tasks 12-13 (unit), Tasks 21-22 (smoke), Task 24 (e2e) |
| §8 Implementation order | This plan's phase numbering |

No spec section is uncovered.
