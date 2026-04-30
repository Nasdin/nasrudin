/// Banner shown on theorem detail when the row is in
/// `status=Rejected` with `rejected_reason` starting `ancestor_rejected:<hex>`.
///
/// Surfaces the cascade transitively: this theorem is rejected because
/// an ancestor was, and the link points the user at that ancestor.
/// The reason format is set by `engine/crates/api/src/reverify.rs::cascade_reject`
/// — `ancestor_rejected: <hex_id>` where `<hex_id>` is the root that
/// was lake-rejected.

import { Link } from '@tanstack/react-router';

interface Props {
  rejectedReason: string;
}

export function CascadeAlert({ rejectedReason }: Props) {
  const rootHex = parseAncestorHex(rejectedReason);
  return (
    <div
      role="alert"
      style={{
        padding: 16,
        background: 'var(--danger-50, #fef2f2)',
        border: '1px solid var(--danger-200, #fecaca)',
        borderLeft: '4px solid var(--danger-500, #ef4444)',
        borderRadius: 'var(--radius-md, 6px)',
        color: 'var(--danger-700, #b91c1c)',
        marginBottom: 24,
      }}
    >
      <div style={{ fontWeight: 700, marginBottom: 6 }}>Cascaded rejection</div>
      <p style={{ margin: 0, fontSize: 14, lineHeight: 1.5 }}>
        This theorem was rejected because an ancestor failed kernel verification. Cascade rejection
        ensures no theorem can stand on a foundation the kernel has refuted.
      </p>
      {rootHex && (
        <p style={{ margin: '8px 0 0', fontSize: 13 }}>
          Root rejection:{' '}
          <Link
            to="/theorem/$id"
            params={{ id: rootHex }}
            style={{ color: 'var(--danger-700)', fontFamily: 'var(--font-mono)' }}
          >
            thm:{rootHex.slice(0, 12)}…
          </Link>
        </p>
      )}
    </div>
  );
}

function parseAncestorHex(reason: string): string | null {
  const prefix = 'ancestor_rejected:';
  if (!reason.startsWith(prefix)) return null;
  const tail = reason.slice(prefix.length).trim();
  // Accept the bare hex form `ancestor_rejected: <hex>` and tolerate a
  // few wrappers like brackets or punctuation.
  const m = tail.match(/[0-9a-fA-F]{16}/);
  return m ? m[0] : null;
}
