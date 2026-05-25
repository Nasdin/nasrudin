import { createFileRoute } from '@tanstack/react-router';
import { useEffect, useRef, useState } from 'react';
import { adminFetch } from '~/lib/adminApi';
import { API_BASE } from '~/lib/api';

export const Route = createFileRoute('/admin/bulk')({ loader: async () => null, component: BulkPage });

type ActionKind = 'set_trust' | 'set_plan' | 'adjust_credits' | 'set_spot_check_rate';

function BulkPage() {
  const [ids, setIds] = useState('');
  const [kind, setKind] = useState<ActionKind>('set_trust');
  const [params, setParams] = useState('{"is_trusted":true}');
  const [reason, setReason] = useState('');
  const [runId, setRunId] = useState<string | null>(null);
  const [events, setEvents] = useState<unknown[]>([]);
  const esRef = useRef<EventSource | null>(null);

  useEffect(() => {
    if (!runId) return;
    const es = new EventSource(`${API_BASE}/api/admin/users/bulk/${runId}/stream`, {
      withCredentials: true,
    });
    const handle = (e: MessageEvent) => {
      try {
        setEvents((prev) => [...prev, JSON.parse(e.data)]);
      } catch {
        /* ignore malformed */
      }
    };
    es.addEventListener('snapshot', handle as EventListener);
    es.addEventListener('progress', handle as EventListener);
    esRef.current = es;
    return () => {
      es.close();
      esRef.current = null;
    };
  }, [runId]);

  const start = async () => {
    if (reason.trim().length < 10) {
      alert('Reason must be at least 10 characters.');
      return;
    }
    let parsedParams: unknown;
    try {
      parsedParams = JSON.parse(params);
    } catch {
      alert('params must be valid JSON.');
      return;
    }
    const userIds = ids
      .split('\n')
      .map((s) => s.trim())
      .filter(Boolean);
    if (userIds.length === 0) {
      alert('At least one user id required.');
      return;
    }
    const r = await adminFetch<{ run_id: string }>('/api/admin/users/bulk', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        action: kind,
        params: parsedParams,
        user_ids: userIds,
        reason: reason.trim(),
      }),
    });
    setEvents([]);
    setRunId(r.run_id);
  };

  return (
    <section>
      <h1>Bulk operations</h1>
      <div style={{ display: 'grid', gridTemplateColumns: '180px 1fr', gap: 12 }}>
        <strong>User IDs</strong>
        <textarea
          rows={6}
          value={ids}
          onChange={(e) => setIds(e.target.value)}
          placeholder="One UUID per line"
          style={{ fontFamily: 'monospace', width: '100%' }}
        />
        <strong>Action</strong>
        <select value={kind} onChange={(e) => setKind(e.target.value as ActionKind)}>
          <option value="set_trust">set_trust</option>
          <option value="set_plan">set_plan</option>
          <option value="adjust_credits">adjust_credits</option>
          <option value="set_spot_check_rate">set_spot_check_rate</option>
        </select>
        <strong>Params (JSON)</strong>
        <input
          value={params}
          onChange={(e) => setParams(e.target.value)}
          style={{ fontFamily: 'monospace', width: '100%' }}
        />
        <strong>Reason</strong>
        <input
          value={reason}
          onChange={(e) => setReason(e.target.value)}
          placeholder="≥ 10 chars"
          style={{ width: '100%' }}
        />
      </div>
      <button onClick={() => void start()} style={{ marginTop: 12 }}>
        Start run
      </button>
      {runId && (
        <>
          <h2 style={{ marginTop: 24 }}>run_id: {runId}</h2>
          <pre style={{ background: 'var(--paper-100)', padding: 12, overflowX: 'auto' }}>
            {JSON.stringify(events, null, 2)}
          </pre>
        </>
      )}
    </section>
  );
}
