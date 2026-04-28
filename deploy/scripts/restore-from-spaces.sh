#!/usr/bin/env bash
# Phase 9 — disaster recovery. Pulls latest backup from DO Spaces, restores
# Postgres, syncs RocksDB, and restarts the stack. Run from the droplet root.
#
# Required env (from /opt/nasrudin/deploy/.env):
#   POSTGRES_USER, POSTGRES_PASSWORD, POSTGRES_DB, DO_SPACES_BUCKET
#
# Side effects: brings the stack DOWN, wipes /data/rocks, restores Postgres
# from dump. Use only when starting from an empty droplet OR when corrupt
# state must be replaced.

set -euo pipefail

cd "$(dirname "$0")/.."   # → /opt/nasrudin/deploy

if [ ! -f .env ]; then
  echo "error: deploy/.env not found; run bootstrap.sh first to populate it"
  exit 1
fi

# Load env
set -a
. .env
set +a

if [ ! -f rclone.conf ]; then
  echo "error: deploy/rclone.conf not found; create it from rclone.conf.example"
  exit 1
fi

# Find the most recent backup directory in Spaces (year/month/day/hour).
LATEST=$(rclone --config rclone.conf lsf "spaces:$DO_SPACES_BUCKET/" --dirs-only --recursive | \
         grep -E '^[0-9]{4}/[0-9]{2}/[0-9]{2}/[0-9]{2}/$' | sort | tail -1)
if [ -z "$LATEST" ]; then
  echo "error: no backups found at spaces:$DO_SPACES_BUCKET/"
  exit 1
fi
LATEST="${LATEST%/}"
echo "[restore] selected backup: $LATEST"

read -p "Type YES to wipe /data/rocks + Postgres and restore from this backup: " ack
if [ "$ack" != "YES" ]; then
  echo "aborted"
  exit 1
fi

# 1. Stop everything
echo "[restore] docker compose down"
docker compose down

# 2. Wipe RocksDB + sync from Spaces
echo "[restore] wiping /data/rocks"
rm -rf /data/rocks/*
echo "[restore] rclone sync rocks/"
rclone --config rclone.conf sync \
  "spaces:$DO_SPACES_BUCKET/$LATEST/rocks/" /data/rocks/

# 3. Pull the Postgres dump
echo "[restore] downloading pg.dump"
rclone --config rclone.conf copy \
  "spaces:$DO_SPACES_BUCKET/$LATEST/pg.dump" /tmp/

# 4. Bring up just Postgres + restore
echo "[restore] starting Postgres"
docker compose up -d postgres
sleep 10

echo "[restore] pg_restore"
docker compose run --rm \
  -v /tmp/pg.dump:/tmp/pg.dump:ro \
  postgres pg_restore \
    -U "$POSTGRES_USER" -h postgres -d "$POSTGRES_DB" -c /tmp/pg.dump

# 5. Bring up the rest
echo "[restore] starting full stack"
docker compose up -d
echo "[restore] waiting 10s for api warmup..."
sleep 10

# 6. Smoke check
echo "[restore] running smoke checks"
NASRUDIN_API_PUBLIC_URL=http://localhost:3001 \
NASRUDIN_FRONTEND_PUBLIC_URL=http://localhost:3000 \
NASRUDIN_INTERNAL_WORKER_KEY="$(grep '^NASRUDIN_INTERNAL_WORKER_KEY=' .env | cut -d= -f2-)" \
  scripts/smoke.sh || echo "[restore] warning: smoke.sh reported failures; investigate before declaring restore successful"

echo "[restore] complete; backup window restored: $LATEST"
