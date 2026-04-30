#!/usr/bin/env bash
# admin-bootstrap.sh — one-time bootstrap for the admin panel.
#
# 1. Promote the supplied email to admin (if it exists in users).
# 2. Create the system actor row with the hardcoded UUID
#    00000000-0000-0000-0000-000000000001 so that audit-log inserts
#    written by the refund reconciler / impersonation expiry tick /
#    AUTO_REVOKE worker logic satisfy the actor_user_id FK constraint.
#
# Idempotent — safe to run multiple times.
#
# Usage:
#   NASRUDIN_DATABASE_URL=postgres://... admin-bootstrap.sh you@example.com

set -euo pipefail

EMAIL="${1:?email required as first argument}"

if [[ -z "${NASRUDIN_DATABASE_URL:-}" ]]; then
  echo "NASRUDIN_DATABASE_URL must be set" >&2
  exit 1
fi

psql "$NASRUDIN_DATABASE_URL" <<SQL
-- Promote the user (no-op if email doesn't exist yet — they need to
-- sign in once first via the Firebase flow to create their users row).
UPDATE users SET is_admin = TRUE WHERE email = '${EMAIL}';

-- System actor for refund-reconciler / auto-revoke / expiry-tick audit
-- rows. firebase_uid is set to a sentinel since this row is never
-- supposed to log in via Firebase.
INSERT INTO users (id, email, plan_tier, is_admin, is_trusted, research_credits, firebase_uid, created_at)
VALUES (
    '00000000-0000-0000-0000-000000000001',
    'system@nasrudin.org',
    'free',
    FALSE,
    FALSE,
    0,
    'system',
    now()
) ON CONFLICT (email) DO NOTHING;
SQL

echo "[admin-bootstrap] '${EMAIL}' is admin (or unchanged); system actor exists"
