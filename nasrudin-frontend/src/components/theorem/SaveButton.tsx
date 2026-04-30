import { Link } from '@tanstack/react-router';
import { useState } from 'react';
import { isApiError } from '~/lib/api';
import {
  useLibraryTheorems,
  useMe,
  useSaveTheorem,
  useUnsaveTheorem,
} from '~/lib/queries';

interface SaveButtonProps {
  theoremIdHex: string;
}

/**
 * Save / unsave button for the theorem detail page. Renders nothing for
 * signed-out users (sign-in CTA pushed to the page itself).
 *
 * On 402 `library_full` (Free user past the 50-cap) shows an upgrade modal.
 */
export function SaveButton({ theoremIdHex }: SaveButtonProps) {
  const me = useMe();
  const list = useLibraryTheorems();
  const save = useSaveTheorem();
  const unsave = useUnsaveTheorem();
  const [showFull, setShowFull] = useState(false);

  if (!me.data) {
    return (
      <Link
        to="/signin"
        search={{ next: `/theorem/${theoremIdHex}` }}
        className="btn btn-ghost"
        style={{ fontSize: 13 }}
      >
        Sign in to save
      </Link>
    );
  }

  const saved = list.data?.saved.some((s) => bytesToHex(s.theorem.id) === theoremIdHex) ?? false;
  const isPending = save.isPending || unsave.isPending;

  const onClick = async () => {
    if (saved) {
      try {
        await unsave.mutateAsync(theoremIdHex);
      } catch (e) {
        console.error('unsave failed', e);
      }
      return;
    }
    try {
      await save.mutateAsync({ theorem_id: theoremIdHex });
    } catch (e) {
      if (isApiError(e) && e.status === 402) {
        setShowFull(true);
      } else {
        console.error('save failed', e);
      }
    }
  };

  return (
    <>
      <button
        type="button"
        className={saved ? 'btn btn-secondary' : 'btn btn-primary'}
        onClick={onClick}
        disabled={isPending}
        style={{ fontSize: 13 }}
        aria-pressed={saved}
      >
        {saved ? '★ Saved' : '☆ Save to library'}
      </button>
      {showFull && (
        <LibraryFullModal
          limit={list.data?.limit ?? 50}
          onClose={() => setShowFull(false)}
        />
      )}
    </>
  );
}

function LibraryFullModal({ limit, onClose }: { limit: number; onClose: () => void }) {
  return (
    <div
      onClick={onClose}
      style={{
        position: 'fixed',
        inset: 0,
        background: 'rgba(0, 0, 0, 0.4)',
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        zIndex: 100,
      }}
    >
      <div
        onClick={(e) => e.stopPropagation()}
        style={{
          background: 'var(--bg-raised, #FBF7EF)',
          padding: 32,
          borderRadius: 12,
          maxWidth: 440,
          boxShadow: '0 20px 60px rgba(0,0,0,0.18)',
        }}
      >
        <span className="overline">Library full</span>
        <h2 style={{ margin: '8px 0 12px', fontSize: 24 }}>
          You've saved <em style={{ color: 'var(--terracotta-700)' }}>{limit}</em> theorems on Free.
        </h2>
        <p style={{ color: 'var(--ink-700)', lineHeight: 1.5, marginBottom: 24 }}>
          Upgrade to <strong>Researcher</strong> for an unlimited library, folders, and private
          notes — plus 10 targeted GA searches a month and 10× the API quota.
        </p>
        <div style={{ display: 'flex', gap: 12 }}>
          <Link to="/pricing" className="btn btn-primary" style={{ flex: 1 }}>
            See Researcher · $19/mo
          </Link>
          <button type="button" className="btn btn-ghost" onClick={onClose}>
            Maybe later
          </button>
        </div>
      </div>
    </div>
  );
}

function bytesToHex(bytes: Uint8Array | number[]): string {
  return Array.from(bytes)
    .map((b) => b.toString(16).padStart(2, '0'))
    .join('');
}
