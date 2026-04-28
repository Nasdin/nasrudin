#!/usr/bin/env bash
# Phase 9 — backup container loop. Runs hourly inside the `backup` service.
# Dumps Postgres, syncs RocksDB to DigitalOcean Spaces, prunes >30d backups.
#
# Required env (from /opt/nasrudin/deploy/.env via docker-compose):
#   POSTGRES_USER, POSTGRES_PASSWORD, POSTGRES_DB, DO_SPACES_BUCKET
# Required mounts:
#   /data:/data:ro
#   /etc/rclone.conf  (from deploy/rclone.conf)
#
# Loop never exits except via SIGTERM.

set -euo pipefail

INTERVAL=${BACKUP_INTERVAL_SECS:-3600}
RETENTION=${BACKUP_RETENTION_DAYS:-30}

log() { echo "[$(date -u +%Y-%m-%dT%H:%M:%SZ)] $*"; }

trap 'log "received SIGTERM, exiting"; exit 0' TERM INT

while true; do
  STAMP=$(date -u +%Y/%m/%d/%H)
  TARGET="${DO_SPACES_BUCKET}/$STAMP"
  log "starting backup window $STAMP -> spaces:$TARGET"

  if ! PGPASSWORD="$POSTGRES_PASSWORD" pg_dump \
      --username="$POSTGRES_USER" --host=postgres --dbname="$POSTGRES_DB" \
      --format=custom --file=/tmp/pg.dump 2>/tmp/pg-dump.err; then
    log "pg_dump failed:"
    cat /tmp/pg-dump.err >&2
    sleep 60
    continue
  fi

  if ! rclone --config /etc/rclone.conf copy /tmp/pg.dump "spaces:$TARGET/" \
      --s3-no-check-bucket --quiet 2>&1; then
    log "rclone postgres copy failed; will retry next window"
    sleep 60
    continue
  fi
  rm -f /tmp/pg.dump

  if ! rclone --config /etc/rclone.conf sync /data/rocks/ "spaces:$TARGET/rocks/" \
      --s3-no-check-bucket --quiet 2>&1; then
    log "rclone rocks sync failed; will retry next window"
    sleep 60
    continue
  fi

  log "backup window $STAMP complete"

  # Prune old backups (best-effort).
  rclone --config /etc/rclone.conf delete \
    --min-age "${RETENTION}d" \
    --s3-no-check-bucket \
    "spaces:$DO_SPACES_BUCKET/" --rmdirs >/dev/null 2>&1 || \
    log "warning: prune step failed"

  log "sleeping $INTERVAL seconds"
  sleep "$INTERVAL"
done
