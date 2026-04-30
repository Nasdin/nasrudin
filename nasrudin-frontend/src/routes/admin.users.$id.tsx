import { createFileRoute } from '@tanstack/react-router';
import { useQuery, useQueryClient } from '@tanstack/react-query';
import { useState } from 'react';
import { adminFetch } from '~/lib/adminApi';
import ConfirmWithReasonModal from '~/components/admin/ConfirmWithReasonModal';
import DataTable from '~/components/admin/DataTable';
import type { AdminUserDetail } from '~/lib/adminTypes';

export const Route = createFileRoute('/admin/users/$id')({ component: UserDetail });

type Pending =
  | { kind: 'admin'; is_admin: boolean }
  | { kind: 'trust'; is_trusted: boolean }
  | { kind: 'spot_check_rate'; rate: number | null }
  | { kind: 'plan'; plan_tier: string }
  | { kind: 'credits'; delta: number }
  | { kind: 'revoke_key'; key_id: string }
  | { kind: 'refund'; charge_id: string; amount_cents: number };

function UserDetail() {
  const { id } = Route.useParams();
  const qc = useQueryClient();
  const { data, refetch } = useQuery<AdminUserDetail>({
    queryKey: ['admin', 'user', id],
    queryFn: () => adminFetch<AdminUserDetail>(`/api/admin/users/${id}`),
  });
  const [tab, setTab] = useState<'overview' | 'trust' | 'billing' | 'keys' | 'audit'>('overview');
  const [pending, setPending] = useState<Pending | null>(null);

  if (!data) return <p>Loading…</p>;
  const u = data.user;

  const startImpersonate = async () => {
    const reason = window.prompt('Reason for impersonating (≥ 10 chars):');
    if (!reason || reason.trim().length < 10) return;
    const r = await adminFetch<{
      token: string;
      session_id: string;
      target_email: string;
      expires_at: string;
    }>(`/api/admin/users/${id}/impersonate`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ duration_seconds: 900, reason: reason.trim() }),
    });
    sessionStorage.setItem('impersonate_token', r.token);
    sessionStorage.setItem('impersonate_session_id', r.session_id);
    sessionStorage.setItem('impersonate_expires_at', String(Date.parse(r.expires_at)));
    sessionStorage.setItem('impersonate_target_email', r.target_email);
    window.location.href = '/';
  };

  const onConfirm = async (reason: string) => {
    if (!pending) return;
    let path = '';
    let method: 'POST' | 'DELETE' = 'POST';
    let body: Record<string, unknown> = { reason };
    switch (pending.kind) {
      case 'admin':
        path = `/api/admin/users/${id}/admin`;
        body = { is_admin: pending.is_admin, reason };
        break;
      case 'trust':
        path = `/api/admin/users/${id}/trust`;
        body = { is_trusted: pending.is_trusted, reason };
        break;
      case 'spot_check_rate':
        path = `/api/admin/users/${id}/spot_check_rate`;
        body = { rate: pending.rate, reason };
        break;
      case 'plan':
        path = `/api/admin/users/${id}/plan`;
        body = { plan_tier: pending.plan_tier, reason };
        break;
      case 'credits':
        path = `/api/admin/users/${id}/credits`;
        body = { delta: pending.delta, reason };
        break;
      case 'revoke_key':
        path = `/api/admin/api_keys/${pending.key_id}`;
        method = 'DELETE';
        break;
      case 'refund':
        path = `/api/admin/users/${id}/refund`;
        body = {
          stripe_charge_id: pending.charge_id,
          amount_cents: pending.amount_cents,
          reason,
        };
        break;
    }
    await adminFetch<unknown>(path, {
      method,
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(body),
    });
    setPending(null);
    qc.invalidateQueries({ queryKey: ['admin', 'user', id] });
    refetch();
  };

  return (
    <section>
      <header style={{ display: 'flex', alignItems: 'center', gap: 16, marginBottom: 16 }}>
        <h1 style={{ margin: 0 }}>{u.email}</h1>
        <button onClick={() => void startImpersonate()} disabled={u.is_admin}>
          Impersonate
        </button>
      </header>
      <nav style={{ display: 'flex', gap: 4, borderBottom: '1px solid var(--paper-300)' }}>
        {(['overview', 'trust', 'billing', 'keys', 'audit'] as const).map((t) => (
          <button
            key={t}
            onClick={() => setTab(t)}
            style={{
              padding: '6px 12px',
              background: tab === t ? 'var(--paper-100)' : 'transparent',
              border: 'none',
              borderBottom: tab === t ? '2px solid var(--ink-700)' : '2px solid transparent',
              cursor: 'pointer',
            }}
          >
            {t}
          </button>
        ))}
      </nav>

      <div style={{ paddingTop: 16 }}>
        {tab === 'overview' && (
          <pre style={{ background: 'var(--paper-100)', padding: 12, overflowX: 'auto' }}>
            {JSON.stringify(u, null, 2)}
          </pre>
        )}
        {tab === 'trust' && (
          <div style={{ display: 'grid', gridTemplateColumns: '180px 1fr', gap: 12 }}>
            <strong>Admin</strong>
            <div>
              {u.is_admin ? 'yes' : 'no'}{' '}
              <button onClick={() => setPending({ kind: 'admin', is_admin: !u.is_admin })}>
                Toggle
              </button>
            </div>
            <strong>Trusted</strong>
            <div>
              {u.is_trusted ? 'yes' : 'no'}{' '}
              <button onClick={() => setPending({ kind: 'trust', is_trusted: !u.is_trusted })}>
                Toggle
              </button>
            </div>
            <strong>Spot check rate</strong>
            <div>
              <input
                type="number"
                defaultValue={u.spot_check_rate ?? ''}
                placeholder="env default"
                id="rate-in"
                style={{ width: 80 }}
              />{' '}
              <button
                onClick={() => {
                  const v = (document.getElementById('rate-in') as HTMLInputElement).value;
                  setPending({
                    kind: 'spot_check_rate',
                    rate: v === '' ? null : Number(v),
                  });
                }}
              >
                Set
              </button>
            </div>
          </div>
        )}
        {tab === 'billing' && (
          <div style={{ display: 'grid', gridTemplateColumns: '180px 1fr', gap: 12 }}>
            <strong>Plan</strong>
            <div>
              {u.plan_tier}{' '}
              <select id="plan-sel" defaultValue={u.plan_tier}>
                <option value="free">free</option>
                <option value="researcher">researcher</option>
                <option value="team">team</option>
                <option value="institution">institution</option>
              </select>{' '}
              <button
                onClick={() => {
                  const v = (document.getElementById('plan-sel') as HTMLSelectElement).value;
                  setPending({ kind: 'plan', plan_tier: v });
                }}
              >
                Apply
              </button>
            </div>
            <strong>Credits</strong>
            <div>
              {u.research_credits}{' '}
              <input type="number" id="credit-delta" placeholder="delta" style={{ width: 80 }} />{' '}
              <button
                onClick={() => {
                  const v = Number(
                    (document.getElementById('credit-delta') as HTMLInputElement).value,
                  );
                  if (Number.isFinite(v)) setPending({ kind: 'credits', delta: v });
                }}
              >
                Adjust
              </button>
            </div>
            <strong>Refund</strong>
            <div>
              <input id="ch-id" placeholder="ch_..." style={{ width: 200 }} />{' '}
              <input
                type="number"
                id="ch-amount"
                placeholder="amount in cents"
                style={{ width: 140 }}
              />{' '}
              <button
                onClick={() => {
                  const ch = (document.getElementById('ch-id') as HTMLInputElement).value.trim();
                  const amt = Number(
                    (document.getElementById('ch-amount') as HTMLInputElement).value,
                  );
                  if (ch && amt > 0)
                    setPending({ kind: 'refund', charge_id: ch, amount_cents: amt });
                }}
              >
                Issue refund
              </button>
            </div>
          </div>
        )}
        {tab === 'keys' && (
          <DataTable
            columns={[
              { key: 'name', header: 'Name' },
              { key: 'kind', header: 'Kind' },
              {
                key: 'revoked_at',
                header: 'Revoked',
                render: (r) => (r.revoked_at ? '✓' : ''),
              },
              {
                key: 'trust_override',
                header: 'Trust',
                render: (r) =>
                  r.trust_override == null ? 'inherit' : String(r.trust_override),
              },
              {
                key: 'id',
                header: 'Actions',
                render: (r) => (
                  <button
                    disabled={!!r.revoked_at}
                    onClick={() => setPending({ kind: 'revoke_key', key_id: r.id })}
                  >
                    Revoke
                  </button>
                ),
              },
            ]}
            rows={data.api_keys}
          />
        )}
        {tab === 'audit' && (
          <pre style={{ background: 'var(--paper-100)', padding: 12, overflowX: 'auto' }}>
            {JSON.stringify(data.recent_audit, null, 2)}
          </pre>
        )}
      </div>

      {pending && (
        <ConfirmWithReasonModal
          title={`Confirm ${pending.kind}`}
          onCancel={() => setPending(null)}
          onConfirm={onConfirm}
        />
      )}
    </section>
  );
}
