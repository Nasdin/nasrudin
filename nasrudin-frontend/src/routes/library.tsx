import { createFileRoute, Link } from '@tanstack/react-router';
import { useVirtualizer } from '@tanstack/react-virtual';
import { type CSSProperties, useRef, useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { SignInPrompt } from '~/components/platform/SignInPrompt';
import { bytesToHex } from '~/lib/hex';
import { Math as MathExpr } from '~/lib/katex';
import {
  type LibraryFolder,
  libraryFoldersOptions,
  libraryTheoremsOptions,
  type SavedTheoremRow,
  useCreateFolder,
  useDeleteFolder,
  useLibraryFolders,
  useLibraryTheorems,
  useMe,
  usePatchFolder,
  usePatchSavedTheorem,
  useSavedSearches,
  useUnsaveTheorem,
} from '~/lib/queries';

export const Route = createFileRoute('/library')({
  // Prefetch library theorems + folders in parallel on hover. Both
  // are user-scoped queries that hit small tables; warming both
  // means the library page hydrates without any network round-trip
  // when the user clicks the nav link. Failures (notably 401 for
  // logged-out visitors) are swallowed — the component renders a
  // SignInPrompt instead of erroring the whole route.
  loader: async ({ context }) => {
    await Promise.all([
      context.queryClient.ensureQueryData(libraryTheoremsOptions()).catch(() => {}),
      context.queryClient.ensureQueryData(libraryFoldersOptions()).catch(() => {}),
    ]);
  },
  component: LibraryPage,
});

type Tab = 'theorems' | 'searches';
type FolderFilter = 'all' | 'ungrouped' | string; // 'all' | 'ungrouped' | uuid

function LibraryPage() {
  const me = useMe();
  const [tab, setTab] = useState<Tab>('theorems');
  const [folderFilter, setFolderFilter] = useState<FolderFilter>('all');

  const apiFolderArg = folderFilter === 'all' ? undefined : folderFilter;
  const lib = useLibraryTheorems(apiFolderArg);
  const folders = useLibraryFolders();
  const saved = useSavedSearches();

  const virtualListRef = useRef<HTMLDivElement>(null);
  const savedTheorems = lib.data?.saved ?? [];

  const virtualizer = useVirtualizer({
    count: savedTheorems.length,
    getScrollElement: () => virtualListRef.current,
    estimateSize: () => 80,
    overscan: 5,
  });

  if (me.isPending) return null;
  if (!me.data)
    return (
      <SignInPrompt
        active="library"
        overline="Your library"
        title="My library"
        description={
          <>
            Save any theorem from <Link to="/browse">the corpus</Link> with the ★ button. Group
            saves into folders and attach private notes for paper drafts or lab notebooks.
          </>
        }
      />
    );

  const allFolders = folders.data?.folders ?? [];
  const totalCount = lib.data?.count ?? 0;
  const limit = lib.data?.limit ?? 50;
  const planTier = lib.data?.plan_tier ?? 'free';
  const isUnlimited = limit > 1_000_000; // u32::MAX coming from prod; treat as ∞
  const savedSearches = saved.data?.saved_searches ?? [];

  return (
    <div className="app">
      <AppHeader active="library" />
      <div className="container-wide">
        <div className="page-head">
          <span className="overline">Your library</span>
          <h1>
            My library —{' '}
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              theorems you've saved + searches you've kept.
            </em>
          </h1>
          <p className="lede">
            Save any theorem from <Link to="/browse">the corpus</Link> with the ★ button. Group
            saves into folders and attach private notes for paper drafts or lab notebooks.
          </p>
          {!isUnlimited && (
            <UsageBar count={totalCount} limit={limit} planTier={planTier} />
          )}
        </div>

        <div className="page-body">
          <div className="lead-tabs" style={{ margin: '0 0 24px' }}>
            <button
              type="button"
              className={`lead-tab ${tab === 'theorems' ? 'active' : ''}`}
              onClick={() => setTab('theorems')}
            >
              Theorems · {totalCount}
            </button>
            <button
              type="button"
              className={`lead-tab ${tab === 'searches' ? 'active' : ''}`}
              onClick={() => setTab('searches')}
            >
              Saved searches · {savedSearches.length}
            </button>
          </div>

          {tab === 'theorems' && (
            <div className="library-grid">
              <FolderSidebar
                folders={allFolders}
                active={folderFilter}
                onSelect={setFolderFilter}
              />
              <div>
                {lib.isPending && <p style={{ color: 'var(--ink-500)' }}>loading…</p>}
                {!lib.isPending && savedTheorems.length === 0 ? (
                  <EmptyState>
                    {folderFilter === 'all' ? (
                      <>
                        You haven't saved any theorems yet. Browse{' '}
                        <Link to="/browse">the corpus</Link> and click ★ on anything you want to
                        come back to.
                      </>
                    ) : (
                      <>This folder is empty. Drop saved theorems into it from the row menu.</>
                    )}
                  </EmptyState>
                ) : (
                  <div
                    ref={virtualListRef}
                    style={{
                      height: 'calc(100vh - 400px)',
                      overflow: 'auto',
                    }}
                  >
                    <div
                      style={{
                        height: `${virtualizer.getTotalSize()}px`,
                        width: '100%',
                        position: 'relative',
                      }}
                    >
                      {virtualizer.getVirtualItems().map((virtualItem) => {
                        const row = savedTheorems[virtualItem.index];
                        if (!row) return null;
                        return (
                          <div
                            key={bytesToHex(row.theorem.id)}
                            style={{
                              position: 'absolute',
                              top: 0,
                              left: 0,
                              width: '100%',
                              transform: `translateY(${virtualItem.start}px)`,
                            }}
                          >
                            <SavedTheoremItem row={row} folders={allFolders} />
                          </div>
                        );
                      })}
                    </div>
                  </div>
                )}
              </div>
            </div>
          )}

          {tab === 'searches' &&
            (savedSearches.length === 0 ? (
              <EmptyState>
                You haven't saved any searches yet. Save a query from{' '}
                <Link to="/browse">the corpus →</Link>
              </EmptyState>
            ) : (
              <ul className="saved-list">
                {savedSearches.map((s) => (
                  <li key={s.id}>
                    <span className="saved-stmt">{s.label ?? s.latex}</span>
                    <span className="saved-domain">search</span>
                    <span className="saved-date">
                      {new Date(s.created_at).toLocaleDateString()}
                    </span>
                  </li>
                ))}
              </ul>
            ))}
        </div>
      </div>
      <AppFooter />
    </div>
  );
}

function UsageBar({
  count,
  limit,
  planTier,
}: {
  count: number;
  limit: number;
  planTier: string;
}) {
  const pct = Math.min(100, Math.round((count / limit) * 100));
  const near = pct >= 80;
  return (
    <div style={{ marginTop: 12, fontSize: 13, color: 'var(--ink-700)' }}>
      <div style={{ display: 'flex', justifyContent: 'space-between', marginBottom: 4 }}>
        <span>
          <strong>{count}</strong> / {limit} saved on {planTier}
        </span>
        {near && (
          <Link to="/pricing" style={{ color: 'var(--terracotta-700)', fontWeight: 600 }}>
            Upgrade for unlimited →
          </Link>
        )}
      </div>
      <div
        style={{
          height: 6,
          background: 'var(--paper-200)',
          borderRadius: 3,
          overflow: 'hidden',
        }}
      >
        <div
          style={{
            width: `${pct}%`,
            height: '100%',
            background: near ? 'var(--terracotta-500)' : 'var(--olive-500)',
            transition: 'width 200ms',
          }}
        />
      </div>
    </div>
  );
}

function FolderSidebar({
  folders,
  active,
  onSelect,
}: {
  folders: LibraryFolder[];
  active: FolderFilter;
  onSelect: (f: FolderFilter) => void;
}) {
  const create = useCreateFolder();
  const del = useDeleteFolder();
  const rename = usePatchFolder();
  const [newName, setNewName] = useState('');
  const [editingId, setEditingId] = useState<string | null>(null);
  const [editingName, setEditingName] = useState('');

  const linkStyle: CSSProperties = {
    display: 'block',
    padding: '6px 10px',
    borderRadius: 6,
    fontSize: 14,
    cursor: 'pointer',
    color: 'var(--ink-800)',
    border: 'none',
    background: 'transparent',
    width: '100%',
    textAlign: 'left',
  };
  const activeStyle: CSSProperties = {
    background: 'var(--paper-200)',
    fontWeight: 600,
  };

  return (
    <aside className="library-folders">
      <div className="overline" style={{ marginBottom: 8 }}>
        Folders
      </div>
      <button
        type="button"
        style={{ ...linkStyle, ...(active === 'all' ? activeStyle : {}) }}
        onClick={() => onSelect('all')}
      >
        All
      </button>
      <button
        type="button"
        style={{ ...linkStyle, ...(active === 'ungrouped' ? activeStyle : {}) }}
        onClick={() => onSelect('ungrouped')}
      >
        Unsorted
      </button>
      <div style={{ height: 1, background: 'var(--paper-200)', margin: '8px 0' }} />
      {folders.map((f) =>
        editingId === f.id ? (
          <form
            key={f.id}
            onSubmit={async (e) => {
              e.preventDefault();
              if (editingName.trim() && editingName !== f.name) {
                await rename.mutateAsync({ id: f.id, patch: { name: editingName.trim() } });
              }
              setEditingId(null);
            }}
            style={{ display: 'flex', gap: 4, marginBottom: 2 }}
          >
            <input
              value={editingName}
              onChange={(e) => setEditingName(e.target.value)}
              autoFocus
              onBlur={() => setEditingId(null)}
              style={{
                flex: 1,
                padding: '4px 8px',
                fontSize: 13,
                border: '1px solid var(--paper-300)',
                borderRadius: 4,
              }}
            />
          </form>
        ) : (
          <div
            key={f.id}
            style={{ display: 'flex', alignItems: 'center', gap: 4 }}
          >
            <button
              type="button"
              style={{
                ...linkStyle,
                ...(active === f.id ? activeStyle : {}),
                flex: 1,
              }}
              onClick={() => onSelect(f.id)}
              onDoubleClick={() => {
                setEditingId(f.id);
                setEditingName(f.name);
              }}
            >
              {f.name}
            </button>
            <button
              type="button"
              onClick={() => {
                if (confirm(`Delete folder "${f.name}"? Theorems become Unsorted.`)) {
                  del.mutate(f.id);
                  if (active === f.id) onSelect('all');
                }
              }}
              style={{
                background: 'transparent',
                border: 'none',
                cursor: 'pointer',
                color: 'var(--ink-400)',
                fontSize: 14,
                padding: '0 4px',
              }}
              title="Delete folder"
            >
              ×
            </button>
          </div>
        ),
      )}
      <form
        onSubmit={async (e) => {
          e.preventDefault();
          if (newName.trim()) {
            try {
              await create.mutateAsync({ name: newName.trim() });
              setNewName('');
            } catch (err) {
              console.error(err);
              alert('Could not create folder (already exists?)');
            }
          }
        }}
        style={{ marginTop: 12 }}
      >
        <input
          value={newName}
          onChange={(e) => setNewName(e.target.value)}
          placeholder="+ New folder"
          maxLength={100}
          style={{
            width: '100%',
            padding: '6px 10px',
            fontSize: 13,
            border: '1px dashed var(--paper-300)',
            borderRadius: 6,
            background: 'transparent',
          }}
        />
      </form>
    </aside>
  );
}

function SavedTheoremItem({
  row,
  folders,
}: {
  row: SavedTheoremRow;
  folders: LibraryFolder[];
}) {
  const id = bytesToHex(row.theorem.id);
  const unsave = useUnsaveTheorem();
  const patch = usePatchSavedTheorem();
  const [noteEdit, setNoteEdit] = useState(false);
  const [noteValue, setNoteValue] = useState(row.note ?? '');

  return (
    <li>
      <Link
        to="/theorem/$id"
        params={{ id }}
        style={{ textDecoration: 'none', color: 'inherit', display: 'contents' }}
      >
        <span className="saved-stmt">
          <MathExpr source={row.theorem.latex ?? row.theorem.canonical_statement} />
        </span>
        <span className="saved-domain">{row.theorem.domain}</span>
        <span className="saved-date">{new Date(row.saved_at).toLocaleDateString()}</span>
      </Link>
      <div
        style={{
          gridColumn: '1 / -1',
          display: 'flex',
          alignItems: 'center',
          gap: 12,
          marginTop: 4,
          fontSize: 12,
        }}
      >
        <select
          value={row.folder_id ?? ''}
          onChange={(e) =>
            patch.mutate({
              theoremIdHex: id,
              patch: { folder_id: e.target.value || null },
            })
          }
          style={{
            fontSize: 12,
            padding: '2px 6px',
            border: '1px solid var(--paper-300)',
            borderRadius: 4,
            background: 'var(--paper-50)',
          }}
        >
          <option value="">Unsorted</option>
          {folders.map((f) => (
            <option key={f.id} value={f.id}>
              {f.name}
            </option>
          ))}
        </select>
        {noteEdit ? (
          <input
            value={noteValue}
            onChange={(e) => setNoteValue(e.target.value)}
            onBlur={() => {
              patch.mutate({
                theoremIdHex: id,
                patch: { note: noteValue || null },
              });
              setNoteEdit(false);
            }}
            onKeyDown={(e) => {
              if (e.key === 'Enter') (e.target as HTMLInputElement).blur();
              if (e.key === 'Escape') {
                setNoteValue(row.note ?? '');
                setNoteEdit(false);
              }
            }}
            placeholder="Private note…"
            style={{
              flex: 1,
              fontSize: 12,
              padding: '2px 6px',
              border: '1px solid var(--paper-300)',
              borderRadius: 4,
            }}
          />
        ) : (
          <button
            type="button"
            onClick={() => setNoteEdit(true)}
            style={{
              flex: 1,
              textAlign: 'left',
              fontSize: 12,
              color: row.note ? 'var(--ink-700)' : 'var(--ink-400)',
              fontStyle: row.note ? 'normal' : 'italic',
              background: 'transparent',
              border: 'none',
              cursor: 'text',
              padding: '2px 0',
            }}
          >
            {row.note ?? 'Add a private note…'}
          </button>
        )}
        <button
          type="button"
          onClick={() => {
            if (confirm('Remove from library?')) unsave.mutate(id);
          }}
          style={{
            background: 'transparent',
            border: 'none',
            cursor: 'pointer',
            color: 'var(--ink-400)',
            fontSize: 13,
            padding: '0 4px',
          }}
          title="Remove"
        >
          ✕
        </button>
      </div>
    </li>
  );
}

function EmptyState({ children }: { children: React.ReactNode }) {
  return (
    <div
      style={{
        padding: '64px 32px',
        textAlign: 'center',
        color: 'var(--ink-500)',
        fontSize: 15,
        border: '1px dashed var(--paper-300)',
        borderRadius: 'var(--radius-lg)',
        background: 'var(--paper-50)',
      }}
    >
      {children}
    </div>
  );
}
