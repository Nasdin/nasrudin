#!/usr/bin/env bash
# Orchestrate a fresh / re-deploy: build artifact → scp → ssh provision.
#
# Usage:
#   deploy/scripts/deploy.sh <DROPLET_NAME_OR_IP> [STRIPE_ENV_FILE]
#
# When a droplet *name* is passed (e.g. `nasrudin-prod`), this script resolves
# the **reserved (static) IP** via doctl. Reserved IPs survive droplet
# rebuilds; the droplet's mutable Public IPv4 (what `doctl compute droplet
# list` returns by default) does not. DNS should always point to the
# reserved IP, so deploying to it is the only way to be sure we're talking
# to the same address Caddy obtained LE certs for.
#
# When an IP literal is passed, it's used verbatim — useful for fresh
# provisioning before a reserved IP is assigned.
#
# STRIPE_ENV_FILE is an optional local file with `KEY=value` lines for the
# Stripe* env vars (see .env.example). It is scp'd to /root/.nasrudin-stripe.env
# on the droplet and merged into /opt/nasrudin/.env by provision-native.sh.

set -euo pipefail
cd "$(dirname "$0")/../.."

TARGET="${1:-}"
STRIPE_FILE="${2:-}"
SSH_OPTS=( -o StrictHostKeyChecking=accept-new -o ConnectTimeout=10 )

if [ -z "$TARGET" ]; then
  echo "usage: $0 <DROPLET_NAME_OR_IP> [STRIPE_ENV_FILE]" >&2
  exit 1
fi

# Resolve droplet name → reserved IP. An IPv4 literal passes through
# unchanged. Any other string is treated as a droplet name and looked up.
if [[ "$TARGET" =~ ^[0-9]{1,3}(\.[0-9]{1,3}){3}$ ]]; then
  IP="$TARGET"
  echo "[deploy] using literal IP $IP"
else
  if ! command -v doctl >/dev/null 2>&1; then
    echo "[deploy] error: doctl not on PATH; can't resolve droplet name '$TARGET'" >&2
    exit 1
  fi
  echo "[deploy] resolving reserved IP for droplet '$TARGET' via doctl…"
  IP="$(doctl compute reserved-ip list --format IP,DropletName --no-header \
        | awk -v name="$TARGET" '$2 == name { print $1; exit }')"
  if [ -z "$IP" ]; then
    echo "[deploy] error: no reserved IP found for droplet '$TARGET'." >&2
    echo "         Reserved IPs survive rebuilds; the droplet's mutable Public IPv4 doesn't." >&2
    echo "         Either assign a reserved IP at" \
         "https://cloud.digitalocean.com/networking/reserved_ips," >&2
    echo "         or pass an IP literal directly." >&2
    exit 1
  fi
  echo "[deploy] resolved $TARGET -> $IP (reserved)"
fi

echo "[deploy] step 1/4: build release artifact"
deploy/scripts/build-release.sh

echo "[deploy] step 2/4: scp artifact -> root@$IP"
ssh "${SSH_OPTS[@]}" "root@$IP" "mkdir -p /root/nasrudin-staging && rm -rf /root/nasrudin-staging/release"
scp "${SSH_OPTS[@]}" dist/release.tar.gz "root@$IP:/root/release.tar.gz"
ssh "${SSH_OPTS[@]}" "root@$IP" "tar xzf /root/release.tar.gz -C /root/nasrudin-staging"

if [ -n "$STRIPE_FILE" ]; then
  [ -f "$STRIPE_FILE" ] || { echo "[deploy] error: $STRIPE_FILE not found" >&2; exit 1; }
  echo "[deploy] step 3/4: scp stripe creds -> /root/.nasrudin-stripe.env"
  scp "${SSH_OPTS[@]}" "$STRIPE_FILE" "root@$IP:/root/.nasrudin-stripe.env"
  ssh "${SSH_OPTS[@]}" "root@$IP" "chmod 600 /root/.nasrudin-stripe.env"
else
  echo "[deploy] step 3/4: skipping stripe creds (no file passed; /api/billing/* will 503)"
fi

echo "[deploy] step 4/4: run provision-native.sh on droplet"
ssh "${SSH_OPTS[@]}" "root@$IP" \
  "/root/nasrudin-staging/release/deploy/scripts/provision-native.sh"

cat <<EOF
[deploy] done. droplet $IP provisioned.
[deploy] next:
  1. point DNS:
       nasrudin.org   A  $IP  (orange-cloud after certs issue)
       api.nasrudin.org   A  $IP  (orange-cloud after certs issue)
       origin.nasrudin.org   A  $IP  (gray-cloud / DNS-only)
     start with all 3 as DNS-only so Caddy can complete LE HTTP-01 challenge.
  2. wait ~60s for Caddy to obtain LE certs, then test:
       curl -fsS https://origin.nasrudin.org/api/health | jq
  3. run full smoke:
       NASRUDIN_API_PUBLIC_URL=https://api.nasrudin.org \\
       NASRUDIN_FRONTEND_PUBLIC_URL=https://nasrudin.org \\
       deploy/scripts/smoke.sh
EOF
