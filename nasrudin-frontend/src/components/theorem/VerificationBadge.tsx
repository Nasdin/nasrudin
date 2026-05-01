import { memo } from 'react';

/// Three-state verification badge mirroring the server's
/// `(status, verification_tactic)` pair.
///
/// - **LakeVerified** (status=Verified, tactic=lake_build): kernel-
///   confirmed; gold-standard for any consumer.
/// - **ChainVerified** (status=Verified, tactic=chain_replay): proven
///   sound by the trusted Rust rule library; provisional, server lake
///   not yet run.
/// - **WorkerClaim** (status=Verified, tactic=worker_claim): a worker
///   reported it lake-built locally; server lake confirmation pending.
/// - **Pending** (status=Pending): submitted, not yet replayed.
/// - **Rejected** (status=Rejected): replay failed or ancestor cascaded.
///
/// Compact mode is a small inline pill for theorem cards; non-compact
/// is the headline pill on detail pages.

interface Props {
  status: string;
  tactic: string | null;
  rejectedReason?: string | null;
  compact?: boolean;
}

interface BadgeStyle {
  label: string;
  bg: string;
  fg: string;
  dot: string;
  hint?: string;
}

function styleOf(s: Props): BadgeStyle {
  if (s.status === 'Rejected') {
    const cascade = s.rejectedReason?.startsWith('ancestor_rejected:') ?? false;
    return {
      label: cascade ? 'Cascaded' : 'Rejected',
      bg: 'var(--danger-50, #fef2f2)',
      fg: 'var(--danger-700, #b91c1c)',
      dot: 'var(--danger-500, #ef4444)',
      hint: cascade
        ? 'An ancestor was rejected; this theorem is invalid by transitivity.'
        : 'Lake build rejected this theorem.',
    };
  }
  if (s.status === 'Pending') {
    return {
      label: 'Pending',
      bg: 'var(--paper-200, #e7e5e4)',
      fg: 'var(--ink-600, #57534e)',
      dot: 'var(--ink-400, #a8a29e)',
      hint: 'Submitted; reverify drain has not run yet.',
    };
  }
  // status=Verified — split by tactic
  switch (s.tactic) {
    case 'lake_build':
      return {
        label: 'Lake-verified',
        bg: 'var(--saffron-100, #fef3c7)',
        fg: 'var(--saffron-800, #92400e)',
        dot: 'var(--saffron-500, #f59e0b)',
        hint: 'Kernel-confirmed by the central server.',
      };
    case 'worker_claim':
      return {
        label: 'Worker-verified',
        bg: 'var(--blue-50, #eff6ff)',
        fg: 'var(--blue-700, #1d4ed8)',
        dot: 'var(--blue-500, #3b82f6)',
        hint: 'A worker lake-built this locally; server lake confirmation pending.',
      };
    default:
      return {
        label: 'Chain-verified',
        bg: 'var(--blue-50, #eff6ff)',
        fg: 'var(--blue-700, #1d4ed8)',
        dot: 'var(--blue-500, #3b82f6)',
        hint: 'Proven by the trusted rule library; lake-build promotion pending.',
      };
  }
}

export const VerificationBadge = memo(function VerificationBadge(props: Props) {
  const s = styleOf(props);
  const compact = props.compact ?? false;
  return (
    <span
      title={s.hint}
      style={{
        display: 'inline-flex',
        alignItems: 'center',
        gap: 6,
        padding: compact ? '2px 8px' : '4px 10px',
        borderRadius: 999,
        background: s.bg,
        color: s.fg,
        fontSize: compact ? 11 : 12,
        fontWeight: 600,
        letterSpacing: 0.3,
        textTransform: 'uppercase',
        whiteSpace: 'nowrap',
      }}
    >
      <span
        aria-hidden
        style={{
          display: 'inline-block',
          width: compact ? 6 : 7,
          height: compact ? 6 : 7,
          borderRadius: '50%',
          background: s.dot,
        }}
      />
      {s.label}
    </span>
  );
});
