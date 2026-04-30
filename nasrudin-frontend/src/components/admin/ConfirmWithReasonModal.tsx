/**
 * Required-reason confirm dialog. Used by every admin mutation so the
 * server-side perform_audited reason ≥ 10 chars validation is satisfied
 * before the request fires.
 */

import { useState } from 'react';

interface Props {
  title: string;
  body?: React.ReactNode;
  confirmLabel?: string;
  onConfirm: (reason: string) => void | Promise<void>;
  onCancel: () => void;
}

export default function ConfirmWithReasonModal({
  title,
  body,
  confirmLabel = 'Confirm',
  onConfirm,
  onCancel,
}: Props) {
  const [reason, setReason] = useState('');
  const [submitting, setSubmitting] = useState(false);
  const valid = reason.trim().length >= 10;

  return (
    <div
      role="dialog"
      aria-modal="true"
      style={{
        position: 'fixed',
        inset: 0,
        background: 'rgba(0, 0, 0, 0.4)',
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        zIndex: 999,
      }}
    >
      <div
        style={{
          background: 'var(--paper-50, #fff)',
          padding: 16,
          borderRadius: 8,
          minWidth: 420,
          maxWidth: 560,
        }}
      >
        <h2 style={{ marginTop: 0 }}>{title}</h2>
        {body}
        <textarea
          placeholder="Reason (at least 10 characters)"
          value={reason}
          onChange={(e) => setReason(e.target.value)}
          rows={3}
          style={{ width: '100%', marginTop: 8, fontFamily: 'inherit' }}
        />
        <div style={{ marginTop: 12, display: 'flex', gap: 8, justifyContent: 'flex-end' }}>
          <button onClick={onCancel} disabled={submitting}>
            Cancel
          </button>
          <button
            disabled={!valid || submitting}
            onClick={async () => {
              setSubmitting(true);
              try {
                await onConfirm(reason.trim());
              } finally {
                setSubmitting(false);
              }
            }}
          >
            {submitting ? '…' : confirmLabel}
          </button>
        </div>
      </div>
    </div>
  );
}
