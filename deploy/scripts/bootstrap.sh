#!/usr/bin/env bash
# Phase 9 — fresh-droplet idempotent setup for nasrudin.org.
#
# Run as root via cloud-init / `--user-data`:
#   doctl compute droplet create … --user-data-file deploy/scripts/bootstrap.sh
#
# Or rerun manually after attaching a Block Volume:
#   ssh root@<droplet-ip>
#   cd /opt/nasrudin/deploy/scripts
#   ./bootstrap.sh
#
# Idempotent: re-running with everything set up is a no-op.

set -euo pipefail

REPO=${REPO:-https://github.com/nasdin/nasrudin.git}
INSTALL_DIR=${INSTALL_DIR:-/opt/nasrudin}
DATA_VOLUME=${DATA_VOLUME:-/dev/disk/by-label/nasrudin-data}
DATA_MOUNT=${DATA_MOUNT:-/data}

log() { echo "[$(date -u +%Y-%m-%dT%H:%M:%SZ)] $*"; }

# --- 1. Apt prerequisites ----------------------------------------------------
log "installing apt prerequisites"
apt-get update
apt-get install -y --no-install-recommends \
  ca-certificates curl gnupg git docker.io docker-compose-v2 ufw openssl

systemctl enable --now docker

# --- 2. Block Volume mount ---------------------------------------------------
log "ensuring data volume mount at $DATA_MOUNT"
mkdir -p "$DATA_MOUNT"
if ! mountpoint -q "$DATA_MOUNT"; then
  if [ -e "$DATA_VOLUME" ]; then
    if ! blkid "$DATA_VOLUME" >/dev/null 2>&1; then
      log "formatting fresh volume $DATA_VOLUME as ext4"
      mkfs.ext4 -L nasrudin-data "$DATA_VOLUME"
    fi
    if ! grep -q "$DATA_VOLUME" /etc/fstab; then
      echo "$DATA_VOLUME $DATA_MOUNT ext4 defaults,nofail,discard 0 2" >> /etc/fstab
    fi
    mount "$DATA_MOUNT"
  else
    log "warning: $DATA_VOLUME not present; using droplet root disk for /data (no Block Volume)"
  fi
fi

mkdir -p "$DATA_MOUNT"/{postgres,rocks,lake-cache,caddy,caddy-config}
chown -R 999:999 "$DATA_MOUNT/postgres" || true   # postgres user inside container

# --- 3. Repo checkout --------------------------------------------------------
if [ ! -d "$INSTALL_DIR" ]; then
  log "cloning $REPO -> $INSTALL_DIR"
  git clone "$REPO" "$INSTALL_DIR"
else
  log "$INSTALL_DIR exists; running git pull"
  git -C "$INSTALL_DIR" pull --ff-only || log "warning: git pull failed; continuing with current checkout"
fi

cd "$INSTALL_DIR/deploy"

# --- 4. .env generation ------------------------------------------------------
if [ ! -f .env ]; then
  log "generating .env from .env.example"
  cp .env.example .env
  # Replace each __GEN__ with an independent 32-byte hex value.
  while grep -q '__GEN__' .env; do
    sed -i "0,/__GEN__/{s/__GEN__/$(openssl rand -hex 32)/}" .env
  done
  chmod 600 .env
  log "secrets generated; backup /opt/nasrudin/deploy/.env securely"
else
  log ".env already present; skipping secret generation"
fi

if [ ! -f rclone.conf ]; then
  log "creating rclone.conf placeholder; fill in DO Spaces creds before backup container starts"
  cp rclone.conf.example rclone.conf
  chmod 600 rclone.conf
fi

# --- 5. UFW firewall ---------------------------------------------------------
log "configuring ufw"
ufw allow 22/tcp
ufw allow 80/tcp
ufw allow 443/tcp
yes | ufw enable

# --- 6. Bring up the stack ---------------------------------------------------
log "pulling + building containers"
docker compose pull
docker compose build

log "starting core services"
docker compose up -d postgres caddy api frontend

log "waiting for postgres + api"
for i in $(seq 1 30); do
  if docker compose exec -T api curl -fsS http://localhost:3001/api/health >/dev/null 2>&1; then
    log "api healthy"
    break
  fi
  sleep 2
done

log "running database migrations"
docker compose run --rm api /usr/local/bin/migrate up

# --- 7. Backfill (idempotent — Duplicate-status submissions are no-ops) ------
if grep -q "^NASRUDIN_BACKFILL_KEY=__GEN__" .env; then
  log "backfill key still placeholder; skipping backfill (run manually after issuing a real key)"
else
  log "running one-shot backfill of prover/Derived/*.lean"
  set +e
  docker compose run --rm \
    -e NASRUDIN_API_URL=http://api:3001 \
    -e NASRUDIN_BACKFILL_KEY="$(grep '^NASRUDIN_BACKFILL_KEY=' .env | cut -d= -f2-)" \
    -e PROVER_ROOT=/opt/prover \
    api /usr/local/bin/backfill_existing_lean
  set -e
fi

# --- 8. Backup container -----------------------------------------------------
if grep -q "REPLACE_ME" rclone.conf; then
  log "rclone.conf still has REPLACE_ME placeholders; not starting backup container"
else
  log "starting backup container"
  docker compose up -d backup
fi

log "Bootstrap complete."
log "Next steps:"
log "  1. Issue a worker key:    docker compose run --rm api /usr/local/bin/migrate    # (issue-worker-key TBD)"
log "  2. Start the GA worker:    docker compose --profile workers up -d ga-worker"
log "  3. Run smoke checks:       deploy/scripts/smoke.sh"
