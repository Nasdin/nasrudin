import { memo } from 'react';

/// Three-state public verification badge.
///
/// Public endpoints filter `tactic=chain_replay` rows server-side (they
/// have no Lean kernel backing), so this component never expects to
/// render one — but if a chain_replay slips through any code path, it
/// falls back to "Pending" rather than implying verification.
///
/// - **Lean-verified (server)** (gold): `tactic=lake_build`, OR
///   `tactic=worker_claim` with `submitterTrusted=true`. Trusted workers
///   lake-build locally and the server skips its own re-build (modulo
///   1-in-N spot-checks); semantically equivalent to a server-confirmed
///   row.
/// - **Lean-verified (worker)** (blue): `tactic=worker_claim` with
///   `submitterTrusted=false`. Worker lake-built locally; server lake
///   confirmation is queued. Tooltip notes "pending server verification".
/// - **Imported (Mathlib/PhysLean)** (terracotta): `tactic=imported`.
///   The theorem comes from an upstream formalisation that Lean already
///   accepted; we do not re-build it server-side and there is no proof
///   we can copy verbatim, but the statement is part of a known-good
///   library.
/// - **Pending** (grey): `status=Pending` OR a leaked chain_replay row.
/// - **Rejected** / **Cascaded** (red): `status=Rejected`. Cascade is
///   detected via `rejectedReason` prefix `ancestor_rejected:`.
///
/// Compact mode is a small inline pill for theorem cards; non-compact
/// is the headline pill on detail pages.

interface Props {
  status: string;
  tactic: string | null;
  submitterTrusted: boolean;
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
  // status=Verified — split by (tactic, submitterTrusted)
  if (s.tactic === 'lake_build') {
    return {
      label: 'Lean-verified (server)',
      bg: 'var(--saffron-100, #fef3c7)',
      fg: 'var(--saffron-800, #92400e)',
      dot: 'var(--saffron-500, #f59e0b)',
      hint: 'Server ran lake build; Lean kernel confirmed.',
    };
  }
  if (s.tactic === 'worker_claim' && s.submitterTrusted) {
    return {
      label: 'Lean-verified (server)',
      bg: 'var(--saffron-100, #fef3c7)',
      fg: 'var(--saffron-800, #92400e)',
      dot: 'var(--saffron-500, #f59e0b)',
      hint: 'Trusted worker lake-built locally; server accepts without re-running.',
    };
  }
  if (s.tactic === 'worker_claim') {
    return {
      label: 'Lean-verified (worker)',
      bg: 'var(--blue-50, #eff6ff)',
      fg: 'var(--blue-700, #1d4ed8)',
      dot: 'var(--blue-500, #3b82f6)',
      hint: 'Worker lake-built locally; server lake confirmation pending.',
    };
  }
  if (s.tactic === 'imported') {
    return {
      label: 'Imported · upstream-verified',
      bg: 'var(--terracotta-50, #fef2f0)',
      fg: 'var(--terracotta-800, #7a2e1a)',
      dot: 'var(--terracotta-500, #d97559)',
      hint: 'Imported from Mathlib / PhysLean — accepted by Lean upstream.',
    };
  }
  // Defense-in-depth fallback for chain_replay or unknown tactic.
  // Public endpoints filter chain_replay out; reaching this branch
  // means a leak — render as Pending, never as verified.
  return {
    label: 'Pending',
    bg: 'var(--paper-200, #e7e5e4)',
    fg: 'var(--ink-600, #57534e)',
    dot: 'var(--ink-400, #a8a29e)',
    hint: 'Verification still in progress.',
  };
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
