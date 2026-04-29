import { createFileRoute, redirect } from '@tanstack/react-router';
import { type FormEvent, useEffect, useState } from 'react';
import { AppFooter } from '~/components/platform/AppFooter';
import { AppHeader } from '~/components/platform/AppHeader';
import { LlmKeysSection } from '~/components/settings/LlmKeysSection';
import { isApiError } from '~/lib/api';
import { useMe, useMeProfile, useUpdateMeProfile } from '~/lib/queries';

export const Route = createFileRoute('/settings')({ component: SettingsPage });

function SettingsPage() {
  const me = useMe();
  const profile = useMeProfile();
  const update = useUpdateMeProfile();

  const [displayName, setDisplayName] = useState('');
  const [handle, setHandle] = useState('');
  const [institution, setInstitution] = useState('');
  const [field, setField] = useState('');
  const [location, setLocation] = useState('');
  const [website, setWebsite] = useState('');
  const [bio, setBio] = useState('');
  const [error, setError] = useState<string | null>(null);
  const [saved, setSaved] = useState(false);

  // Hydrate form from server state once it arrives.
  useEffect(() => {
    if (!profile.data) return;
    setDisplayName(profile.data.display_name ?? '');
    const p = profile.data.profile;
    setHandle(p.handle ?? '');
    setInstitution(p.institution ?? '');
    setField(p.field ?? '');
    setLocation(p.location ?? '');
    setWebsite(p.website ?? '');
    setBio(p.bio ?? '');
  }, [profile.data]);

  if (me.isPending) return null;
  if (!me.data) throw redirect({ to: '/signin' });

  async function onSubmit(e: FormEvent) {
    e.preventDefault();
    setError(null);
    setSaved(false);
    try {
      const profileFields: Record<string, string> = {};
      if (handle.trim()) profileFields.handle = handle.trim();
      if (institution.trim()) profileFields.institution = institution.trim();
      if (field.trim()) profileFields.field = field.trim();
      if (location.trim()) profileFields.location = location.trim();
      if (website.trim()) profileFields.website = website.trim();
      if (bio.trim()) profileFields.bio = bio.trim();
      await update.mutateAsync({
        display_name: displayName.trim() || null,
        profile: profileFields,
      });
      setSaved(true);
    } catch (e) {
      if (isApiError(e)) {
        const msg =
          e.body && typeof e.body === 'object' && 'error' in e.body
            ? String((e.body as { error: unknown }).error)
            : `Request failed (${e.status})`;
        setError(msg);
      } else {
        setError('Network error');
      }
    }
  }

  return (
    <div className="app">
      <AppHeader active="settings" />
      <div className="container-wide" style={{ maxWidth: 760 }}>
        <div className="page-head">
          <span className="overline">Account</span>
          <h1>
            Settings —{' '}
            <em
              style={{
                fontStyle: 'italic',
                color: 'var(--terracotta-700)',
                fontWeight: 300,
              }}
            >
              your academic profile.
            </em>
          </h1>
          <p className="lede">
            Public fields appear next to theorems you've contributed and on every worker your
            account runs. Email is never published.
          </p>
        </div>

        <form className="page-body" onSubmit={onSubmit} style={{ maxWidth: 560 }}>
          <SectionH>Identity</SectionH>
          <Field
            id="display_name"
            label="Display name"
            value={displayName}
            onChange={setDisplayName}
            placeholder="Anya Klint"
            hint="Shown on your theorems and your workers' contributions."
          />
          <Field
            id="handle"
            label="Public handle"
            value={handle}
            onChange={setHandle}
            placeholder="aklint"
            hint="A short, URL-safe handle. Used for @-mentions and worker attribution."
          />
          <Field
            id="email"
            label="Email"
            value={me.data.email}
            onChange={() => {}}
            readOnly
            hint="Email cannot be changed here. Contact support to migrate."
          />

          <SectionH style={{ marginTop: 40 }}>Affiliation</SectionH>
          <Field
            id="institution"
            label="Institution"
            value={institution}
            onChange={setInstitution}
            placeholder="ETH Zürich"
          />
          <Field
            id="field"
            label="Field"
            value={field}
            onChange={setField}
            placeholder="Theoretical physics"
          />
          <Field
            id="location"
            label="Location"
            value={location}
            onChange={setLocation}
            placeholder="Zürich, CH"
          />
          <Field
            id="website"
            label="Website"
            value={website}
            onChange={setWebsite}
            placeholder="https://your.site"
          />

          <SectionH style={{ marginTop: 40 }}>Bio</SectionH>
          <div className="field">
            <label htmlFor="bio">A short bio</label>
            <textarea
              id="bio"
              value={bio}
              onChange={(e) => setBio(e.target.value)}
              rows={4}
              placeholder="Working on emergent gauge symmetries in lattice models. Using Nasrudin to surface unexpected lemmas in SU(2) commutator algebras."
              style={{
                background: 'var(--bg-raised)',
                border: '1px solid var(--paper-200)',
                borderRadius: 'var(--radius-md)',
                padding: '12px 14px',
                fontFamily: 'var(--font-sans)',
                fontSize: 15,
                color: 'var(--ink-900)',
                resize: 'vertical',
              }}
            />
            <span className="hint">Up to a few sentences. Markdown is rendered as plain text.</span>
          </div>

          {error && (
            <div role="alert" style={{ color: 'var(--danger-500)', fontSize: 13, marginTop: 12 }}>
              {error}
            </div>
          )}
          {saved && !error && (
            <div
              style={{
                color: 'var(--olive-700)',
                marginTop: 12,
                fontFamily: 'var(--font-hand)',
                fontWeight: 500,
                fontSize: 22,
              }}
            >
              Saved. ✓
            </div>
          )}
          <div style={{ marginTop: 24, display: 'flex', gap: 12 }}>
            <button type="submit" className="btn btn-primary" disabled={update.isPending}>
              {update.isPending ? 'Saving…' : 'Save profile'}
            </button>
          </div>
        </form>

        <LlmKeysSection />
      </div>
      <AppFooter />
    </div>
  );
}

function SectionH({ children, style }: { children: React.ReactNode; style?: React.CSSProperties }) {
  return (
    <h3 className="section-h" style={{ fontSize: 22, marginBottom: 16, ...style }}>
      {children}
    </h3>
  );
}

function Field({
  id,
  label,
  value,
  onChange,
  placeholder,
  hint,
  readOnly,
}: {
  id: string;
  label: string;
  value: string;
  onChange: (v: string) => void;
  placeholder?: string;
  hint?: string;
  readOnly?: boolean;
}) {
  return (
    <div className="field">
      <label htmlFor={id}>{label}</label>
      <input
        id={id}
        type="text"
        value={value}
        onChange={(e) => onChange(e.target.value)}
        placeholder={placeholder}
        readOnly={readOnly}
        style={readOnly ? { background: 'var(--paper-100)', color: 'var(--ink-500)' } : undefined}
      />
      {hint && <span className="hint">{hint}</span>}
    </div>
  );
}
