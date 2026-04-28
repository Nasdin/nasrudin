# syntax=docker/dockerfile:1.7

# ──────────────────────────────────────────────────────────────────────────
# Backup container: postgresql-client (for pg_dump) + rclone for offsite
# upload. Run loop is implemented by deploy/scripts/backup-loop.sh.
#
# Build context is the monorepo root (compose uses `context: ..`).
# ──────────────────────────────────────────────────────────────────────────
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates postgresql-client rclone tini \
    && rm -rf /var/lib/apt/lists/*

COPY deploy/scripts/backup-loop.sh /usr/local/bin/backup-loop.sh
RUN chmod +x /usr/local/bin/backup-loop.sh

ENTRYPOINT ["/usr/bin/tini", "--"]
CMD ["/usr/local/bin/backup-loop.sh"]
