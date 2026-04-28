#!/usr/bin/env bash
# Placeholder — Phase 9 Task 9.4 will replace this with the real backup loop
# (pg_dump → /data/backups, rclone copy to offsite). Until then we just idle
# so the container stays running and `docker compose up` doesn't crash-loop.
set -euo pipefail
echo "[backup] Phase 9 Task 9.4 will replace this; idling for now."
while true; do
    sleep 3600
done
