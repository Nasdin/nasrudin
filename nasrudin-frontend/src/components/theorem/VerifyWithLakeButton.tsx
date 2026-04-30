import { useState } from 'react';
import { isApiError } from '~/lib/api';
import { useVerifyWithLake } from '~/lib/queries';

/// Real "Verify with Lake" button — POSTs to `/api/theorems/{id}/verify`,
/// which enqueues a priority-0 lake-promotion and waits up to
/// `wait_seconds` synchronously for the kernel's verdict.
///
/// Outcomes:
/// - 200 + `status=lake_verified` — gold standard reached. Show
///   confetti-grade success and tell the parent to refetch.
/// - 410 + `status=rejected` — kernel rejected. Show the reason; if
///   the reason starts with `ancestor_rejected:`, link to the cascade
///   alert below.
/// - 202 + `Retry-After: 60` — sync wait timed out, promotion is in
///   flight. Show a "still running" state and let the user retry.

interface Props {
  /// Hex-encoded 8-byte canonical hash. Same value as the theorem's
  /// `id` in Phase 9 — `bytesToHex(thm.id)`.
  theoremIdHex: string;
  /// Called after a successful verify so the parent can refetch and
  /// re-render the badge.
  onVerified?: () => void;
}

export function VerifyWithLakeButton({ theoremIdHex, onVerified }: Props) {
  const verify = useVerifyWithLake();
  const [resultLine, setResultLine] = useState<string | null>(null);
  const [resultKind, setResultKind] = useState<'ok' | 'pending' | 'rejected' | null>(null);

  async function run() {
    setResultLine(null);
    setResultKind(null);
    try {
      const r = await verify.mutateAsync({ idHex: theoremIdHex, waitSeconds: 30 });
      const status = r.status ?? 'unknown';
      if (status === 'lake_verified') {
        setResultKind('ok');
        setResultLine('✓ Verified by the kernel. The badge above will refresh.');
        onVerified?.();
      } else if (status === 'rejected') {
        setResultKind('rejected');
        setResultLine(`Kernel rejected: ${r.reason ?? '(no reason)'}`);
      } else if (status === 'pending') {
        setResultKind('pending');
        setResultLine(
          'Lake build is still running. Try again in ~60 seconds — the corpus will pick it up automatically.',
        );
      } else {
        setResultKind('pending');
        setResultLine(`Unexpected response: ${JSON.stringify(r)}`);
      }
    } catch (e) {
      setResultKind('rejected');
      if (isApiError(e)) {
        if (e.status === 429) {
          setResultLine(
            "You've hit the manual-verify rate limit (10/hour). Wait a bit and try again.",
          );
        } else if (e.status === 401) {
          setResultLine('Sign in to manually verify a theorem.');
        } else if (e.status === 404) {
          setResultLine('Theorem not found.');
        } else {
          setResultLine(`Request failed (${e.status})`);
        }
      } else {
        setResultLine('Network error');
      }
    }
  }

  return (
    <div>
      <button type="button" className="btn btn-primary" onClick={run} disabled={verify.isPending}>
        {verify.isPending ? 'Verifying with lake…' : 'Verify with Lake'}
      </button>
      {resultLine && (
        <output
          style={{
            display: 'block',
            marginTop: 12,
            fontSize: 13,
            color:
              resultKind === 'ok'
                ? 'var(--success-700, #15803d)'
                : resultKind === 'rejected'
                  ? 'var(--danger-700, #b91c1c)'
                  : 'var(--ink-600, #57534e)',
          }}
        >
          {resultLine}
        </output>
      )}
    </div>
  );
}
