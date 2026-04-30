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
 * The badge in the corner is the only thing that makes it unambiguous
 * that this is a recording — not a live feed.
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

  if (lines.length === 0) {
    return (
      <div className="install-cli terminal-preview">
        <div className="install-cli-bar">
          <div className="cli-dot" />
          <div className="cli-dot" />
          <div className="cli-dot" />
          <span className="cli-title">~/nasrudin-worker · ./run.sh</span>
          <span className="cli-badge">captured trace pending</span>
        </div>
        <div className="install-cli-body" style={{ color: 'var(--ink-500)' }}>
          A real ./run.sh capture will land here once the binary ships.
        </div>
      </div>
    );
  }

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
