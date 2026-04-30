import { Link } from '@tanstack/react-router';
import { useMemo, useState } from 'react';
import { type ArchKind, detectPlatform, type OsKind } from './RunWorker.platform';
import { runWorkerFixture } from './run-worker.fixture';
import { TerminalPreview } from './TerminalPreview';

const RELEASE_BASE = 'https://github.com/Nasdin/nasrudin/releases/latest/download';

interface Build {
  os: OsKind;
  arch: ArchKind;
  ext: 'tar.gz' | 'zip';
  label: string;
  archLabel: string;
}

const BUILDS: Build[] = [
  {
    os: 'macos',
    arch: 'aarch64',
    ext: 'tar.gz',
    label: 'macOS · Apple Silicon',
    archLabel: 'aarch64-apple-darwin',
  },
  {
    os: 'macos',
    arch: 'x86_64',
    ext: 'tar.gz',
    label: 'macOS · Intel',
    archLabel: 'x86_64-apple-darwin',
  },
  {
    os: 'linux',
    arch: 'x86_64',
    ext: 'tar.gz',
    label: 'Linux · x86_64',
    archLabel: 'x86_64-unknown-linux-gnu',
  },
  {
    os: 'linux',
    arch: 'aarch64',
    ext: 'tar.gz',
    label: 'Linux · aarch64',
    archLabel: 'aarch64-unknown-linux-gnu',
  },
  {
    os: 'windows',
    arch: 'x86_64',
    ext: 'zip',
    label: 'Windows · x86_64',
    archLabel: 'x86_64-pc-windows-gnu',
  },
];

const ELAN_UNIX =
  'curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y';
const ELAN_WIN =
  'iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex';

// Maps the platform-detection model (which uses canonical UA-friendly names
// like "macos" and "aarch64") to the names used by build-worker-all.sh,
// which uses Rust target conventions ("darwin" and "arm64" on macOS).
function bundleSuffix(b: Build): string {
  const osPart = b.os === 'macos' ? 'darwin' : b.os;
  const archPart = b.os === 'macos' && b.arch === 'aarch64' ? 'arm64' : b.arch;
  return `${osPart}-${archPart}`;
}
function bundleName(b: Build): string {
  return `nasrudin-worker-${bundleSuffix(b)}`;
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

  const macBuild = BUILDS.find(
    (b) => b.os === 'macos' && b.arch === (detected?.os === 'macos' ? detected.arch : 'aarch64'),
  ) as Build;
  const linuxBuild = BUILDS.find(
    (b) => b.os === 'linux' && b.arch === (detected?.os === 'linux' ? detected.arch : 'x86_64'),
  ) as Build;
  const winBuild = BUILDS.find((b) => b.os === 'windows') as Build;

  const myBuild: Build = detected
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
              <CodeBlock>{runTab === 'unix' ? extractRunUnix(myBuild) : EXTRACT_RUN_WIN}</CodeBlock>
              <p className="margin-note" style={{ marginTop: 12 }}>
                First run warms the Mathlib cache (a few minutes); next runs reuse it. Ctrl+C is
                clean.
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
          A modest desktop or cloud VM is enough. The harder you push, the faster physics arrives.
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
