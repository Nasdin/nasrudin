#!/usr/bin/env bash
# Native (no-docker) provisioner for the nasrudin-prod droplet (Ubuntu 24.04 LTS).
# Idempotent — safe to re-run.
#
# Run on the droplet as root, after the release tarball has been extracted to
# /root/nasrudin-staging:
#
#     scp dist/release.tar.gz root@$IP:/root/release.tar.gz
#     ssh root@$IP "mkdir -p /root/nasrudin-staging && \
#                   tar xzf /root/release.tar.gz -C /root/nasrudin-staging && \
#                   /root/nasrudin-staging/release/deploy/scripts/provision-native.sh"
#
# Optional: place stripe creds at /root/.nasrudin-stripe.env first
# (KEY=value lines for STRIPE_*); they are merged into /opt/nasrudin/.env.

set -euo pipefail

STAGING="${STAGING:-/root/nasrudin-staging/release}"
INSTALL=/opt/nasrudin
DATA=/var/lib/nasrudin

log() { echo "[provision $(date -u +%H:%M:%S)] $*"; }
[ "$(id -u)" -eq 0 ] || { echo "must run as root" >&2; exit 1; }
[ -d "$STAGING" ] || { echo "staging dir $STAGING not found" >&2; exit 1; }

export DEBIAN_FRONTEND=noninteractive

# ── 1. Apt prerequisites + repos ──────────────────────────────────────────
log "apt update + base packages"
apt-get update -qq
apt-get install -y --no-install-recommends \
  ca-certificates curl gnupg git ufw openssl rsync \
  build-essential pkg-config libssl-dev jq \
  python3 python3-argon2 python3-psycopg2

if ! [ -f /etc/apt/sources.list.d/pgdg.list ]; then
  log "adding PostgreSQL PGDG repo (postgres-18)"
  install -d /usr/share/postgresql-common/pgdg
  curl -fsS https://www.postgresql.org/media/keys/ACCC4CF8.asc \
    -o /usr/share/postgresql-common/pgdg/apt.postgresql.org.asc
  CODENAME="$(. /etc/os-release; echo "$VERSION_CODENAME")"
  echo "deb [signed-by=/usr/share/postgresql-common/pgdg/apt.postgresql.org.asc] https://apt.postgresql.org/pub/repos/apt ${CODENAME}-pgdg main" \
    > /etc/apt/sources.list.d/pgdg.list
  apt-get update -qq
fi

if ! command -v node >/dev/null 2>&1 || ! node --version | grep -q '^v22'; then
  log "adding NodeSource repo (node 22)"
  curl -fsSL https://deb.nodesource.com/setup_22.x | bash - >/dev/null
fi

if ! [ -f /etc/apt/sources.list.d/caddy-stable.list ]; then
  log "adding Caddy stable repo"
  curl -1sLf https://dl.cloudsmith.io/public/caddy/stable/gpg.key \
    | gpg --dearmor -o /usr/share/keyrings/caddy-stable-archive-keyring.gpg
  curl -1sLf https://dl.cloudsmith.io/public/caddy/stable/debian.deb.txt \
    > /etc/apt/sources.list.d/caddy-stable.list
  apt-get update -qq
fi

log "installing postgres-18, node 22, caddy"
apt-get install -y --no-install-recommends \
  postgresql-18 postgresql-client-18 \
  nodejs \
  caddy

# ── 2. Postgres role + db ─────────────────────────────────────────────────
log "configuring postgres role + db"
systemctl enable --now postgresql
PG_USER=physics
PG_DB=physics_generator
PG_PASSWORD_FILE=/etc/nasrudin-pg-password
if [ ! -f "$PG_PASSWORD_FILE" ]; then
  openssl rand -hex 24 > "$PG_PASSWORD_FILE"
  chmod 600 "$PG_PASSWORD_FILE"
fi
PG_PASSWORD="$(cat "$PG_PASSWORD_FILE")"

sudo -u postgres psql -tAc "SELECT 1 FROM pg_roles WHERE rolname='$PG_USER'" | grep -q 1 \
  || sudo -u postgres psql -c "CREATE ROLE $PG_USER WITH LOGIN PASSWORD '$PG_PASSWORD'" >/dev/null
sudo -u postgres psql -c "ALTER ROLE $PG_USER WITH PASSWORD '$PG_PASSWORD'" >/dev/null

sudo -u postgres psql -tAc "SELECT 1 FROM pg_database WHERE datname='$PG_DB'" | grep -q 1 \
  || sudo -u postgres psql -c "CREATE DATABASE $PG_DB OWNER $PG_USER" >/dev/null

# ── 3. nasrudin user + dirs ────────────────────────────────────────────────
log "creating nasrudin system user + dirs"
id -u nasrudin >/dev/null 2>&1 \
  || useradd --system --create-home --home-dir /var/lib/nasrudin --shell /usr/sbin/nologin nasrudin
install -d -o nasrudin -g nasrudin "$INSTALL" "$INSTALL/bin" "$INSTALL/frontend" "$INSTALL/prover" "$INSTALL/elan"
install -d -o nasrudin -g nasrudin "$DATA" "$DATA/rocks" "$DATA/lake-cache"

# ── 4. Stage application files ────────────────────────────────────────────
log "syncing artifact -> $INSTALL"
rsync -a --delete "$STAGING/bin/"      "$INSTALL/bin/"
rsync -a --delete "$STAGING/frontend/" "$INSTALL/frontend/"
rsync -a --delete "$STAGING/prover/"   "$INSTALL/prover/"
chown -R nasrudin:nasrudin "$INSTALL"

# ── 5. .env generation ────────────────────────────────────────────────────
ENV_FILE="$INSTALL/.env"
if [ ! -f "$ENV_FILE" ]; then
  log "generating $ENV_FILE"
  cp "$STAGING/.env.example" "$ENV_FILE"
  while grep -q '__GEN__' "$ENV_FILE"; do
    sed -i "0,/__GEN__/{s/__GEN__/$(openssl rand -hex 32)/}" "$ENV_FILE"
  done

  # Inject postgres + service URLs
  sed -i "s|^POSTGRES_USER=.*|POSTGRES_USER=$PG_USER|"           "$ENV_FILE"
  sed -i "s|^POSTGRES_PASSWORD=.*|POSTGRES_PASSWORD=$PG_PASSWORD|" "$ENV_FILE"
  sed -i "s|^POSTGRES_DB=.*|POSTGRES_DB=$PG_DB|"                 "$ENV_FILE"
  sed -i "s|^POSTGRES_PORT=.*|POSTGRES_PORT=5432|"               "$ENV_FILE"
  sed -i "s|^DATABASE_URL=.*|DATABASE_URL=postgresql://$PG_USER:$PG_PASSWORD@127.0.0.1:5432/$PG_DB|" "$ENV_FILE"
  sed -i "s|^API_PORT=.*|API_PORT=3001|"                         "$ENV_FILE"
  sed -i "s|^VITE_API_URL=.*|VITE_API_URL=https://api.nasrudin.org|" "$ENV_FILE"
  sed -i "s|^ROCKS_DB_PATH=.*|ROCKS_DB_PATH=/var/lib/nasrudin/rocks|" "$ENV_FILE"

  chmod 600 "$ENV_FILE"
  chown nasrudin:nasrudin "$ENV_FILE"
fi

# Stripe overrides — applied EVERY run so a later re-deploy with the file
# populated (sk_live_…, whsec_…) overwrites placeholder values.
if [ -f /root/.nasrudin-stripe.env ]; then
  log "merging stripe creds from /root/.nasrudin-stripe.env"
  while IFS='=' read -r key val; do
    [ -z "$key" ] && continue
    [[ "$key" =~ ^[[:space:]]*# ]] && continue
    sed -i "s#^${key}=.*#${key}=${val}#" "$ENV_FILE"
  done < /root/.nasrudin-stripe.env
  chmod 600 "$ENV_FILE"
  chown nasrudin:nasrudin "$ENV_FILE"
else
  log "no /root/.nasrudin-stripe.env present — Stripe stays placeholder; /api/billing/* will return 503"
fi

# ── 6. Elan + Lean toolchain (pre-built oleans via `lake exe cache get`) ──
ELAN_HOME=$INSTALL/elan
LEAN_TC="$(tr -d '[:space:]' < "$INSTALL/prover/lean-toolchain")"
if [ ! -x "$ELAN_HOME/bin/elan" ]; then
  log "installing elan ($LEAN_TC) under $ELAN_HOME"
  sudo -u nasrudin env ELAN_HOME="$ELAN_HOME" bash -c "
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --no-modify-path --default-toolchain '$LEAN_TC'
  "
else
  log "elan already installed; ensuring toolchain $LEAN_TC is current"
  # elan 4.x's `toolchain install` doesn't accept --no-self-update
  # (only `elan-init.sh` does during initial bootstrap). It also exits
  # non-zero with "already installed" — which is a success state for
  # us — so we swallow that specific outcome.
  sudo -u nasrudin env ELAN_HOME="$ELAN_HOME" PATH="$ELAN_HOME/bin:$PATH" bash -c "
    out=\$(elan toolchain install '$LEAN_TC' 2>&1) || \
      echo \"\$out\" | grep -q 'already installed' || \
      { echo \"\$out\" >&2; exit 1; }
  "
fi
chown -R nasrudin:nasrudin "$ELAN_HOME"

log "warming Mathlib cache via 'lake exe cache get' (downloads pre-built oleans)..."
sudo -u nasrudin env ELAN_HOME="$ELAN_HOME" PATH="$ELAN_HOME/bin:/usr/bin:/bin" bash -c "
  cd $INSTALL/prover
  lake exe cache get || echo '[provision] WARN: lake cache get failed; first lake build will rebuild Mathlib'
"

# ── 7. Caddyfile ──────────────────────────────────────────────────────────
log "installing /etc/caddy/Caddyfile"
install -m 0644 "$STAGING/deploy/Caddyfile" /etc/caddy/Caddyfile
systemctl enable caddy

# ── 8. Systemd units ──────────────────────────────────────────────────────
log "installing systemd units"
install -m 0644 "$STAGING/deploy/systemd/nasrudin-api.service" /etc/systemd/system/
install -m 0644 "$STAGING/deploy/systemd/nasrudin-frontend.service" /etc/systemd/system/
install -m 0644 "$STAGING/deploy/systemd/nasrudin-worker.service" /etc/systemd/system/
install -m 0755 "$STAGING/deploy/scripts/issue_worker_key.py" /opt/nasrudin/bin/issue_worker_key.py
mkdir -p /var/lib/nasrudin/lake-cache /var/lib/nasrudin/rocks-worker
chown -R nasrudin:nasrudin /var/lib/nasrudin
systemctl daemon-reload

# ── 9. Run migrations ─────────────────────────────────────────────────────
log "running database migrations"
sudo -u nasrudin bash -c "
  set -a; . $INSTALL/.env; set +a
  $INSTALL/bin/migrate up
"

# ── 10. UFW + start services ──────────────────────────────────────────────
log "configuring ufw"
ufw allow 22/tcp
ufw allow 80/tcp
ufw allow 443/tcp
yes | ufw enable >/dev/null 2>&1 || true

log "(re)starting services"
systemctl restart caddy
systemctl enable --now nasrudin-api
systemctl enable --now nasrudin-frontend
systemctl restart nasrudin-api nasrudin-frontend
# nasrudin-worker is co-located with the api. We enable it but only start it
# automatically when NASRUDIN_WORKER_KEY is already set in /opt/nasrudin/.env;
# otherwise the operator runs deploy/scripts/issue_worker_key.py first to mint
# a key, then `systemctl start nasrudin-worker` once it's been added.
systemctl enable nasrudin-worker
if grep -q '^NASRUDIN_WORKER_KEY=' /opt/nasrudin/.env; then
  systemctl restart nasrudin-worker
  log "nasrudin-worker restarted (NASRUDIN_WORKER_KEY found in .env)"
else
  log "nasrudin-worker enabled but NOT started — set NASRUDIN_WORKER_KEY in /opt/nasrudin/.env first:"
  log "    KEY=\$(sudo -u nasrudin /opt/nasrudin/bin/issue_worker_key.py nasrudin-prod-droplet)"
  log "    echo \"NASRUDIN_WORKER_KEY=\$KEY\" | sudo -u nasrudin tee -a /opt/nasrudin/.env"
  log "    sudo systemctl start nasrudin-worker"
fi

log "done. service status:"
systemctl --no-pager --lines=0 status nasrudin-api nasrudin-frontend nasrudin-worker caddy postgresql 2>&1 | head -50 || true

cat <<EOF

[provision] complete.
[provision] next steps:
  1. point DNS at this droplet (see deploy/README or your Cloudflare dashboard).
  2. run smoke test from a dev machine:
       NASRUDIN_API_PUBLIC_URL=https://api.nasrudin.org \\
       NASRUDIN_FRONTEND_PUBLIC_URL=https://nasrudin.org \\
       deploy/scripts/smoke.sh
  3. tail logs with:  journalctl -fu nasrudin-api  (or nasrudin-frontend, caddy)
EOF
