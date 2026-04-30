#!/usr/bin/env python3
"""
Issue a fresh nsk_worker_<base32> key directly against the droplet's
Postgres. Reads DATABASE_URL from /opt/nasrudin/.env. Inserts a row into
api_keys (kind='worker', user_id=NULL) and prints the full secret to
stdout. The Argon2 hash is computed via argon2-cffi using the same
algorithm (Argon2id, PHC-encoded) the Rust `password_auth` crate verifies.

Usage:
    sudo python3 issue_worker_key.py [name]

If `name` is omitted, defaults to "platform-droplet".
"""
import base64
import os
import secrets
import sys
import uuid

# argon2-cffi + psycopg2 are installed via apt or pip prior to running
from argon2 import PasswordHasher
import psycopg2

ENV_FILE = "/opt/nasrudin/.env"
NAME = sys.argv[1] if len(sys.argv) > 1 else "platform-droplet"


def load_env(path: str) -> dict[str, str]:
    out: dict[str, str] = {}
    with open(path) as fh:
        for raw in fh:
            line = raw.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            k, _, v = line.partition("=")
            v = v.strip().strip('"').strip("'")
            out[k.strip()] = v
    return out


env = load_env(ENV_FILE)
db_url = env.get("DATABASE_URL") or os.environ.get("DATABASE_URL")
if not db_url:
    sys.exit(f"DATABASE_URL not in {ENV_FILE} or env")

# 1. random secret — same shape as Rust keygen.rs
random_bytes = secrets.token_bytes(24)
secret_lower = base64.b32encode(random_bytes).decode().lower().rstrip("=")
full = f"nsk_worker_{secret_lower}"
prefix = full[:14]

# 2. Argon2id hash — PHC string. Defaults are Argon2id with sane params;
#    the Rust verifier reads params from the PHC string itself, so any
#    Argon2id PHC verifies.
ph = PasswordHasher()
key_hash = ph.hash(full)

# 3. Insert. INSERT into api_keys (id, user_id, kind, name, prefix,
#    key_hash, created_at). The schema requires non-null id/kind/name/
#    prefix/key_hash/created_at; user_id, last_used_at, expires_at,
#    revoked_at are nullable.
conn = psycopg2.connect(db_url)
try:
    with conn, conn.cursor() as cur:
        cur.execute(
            """
            INSERT INTO api_keys
                (id, user_id, kind, name, prefix, key_hash, created_at)
            VALUES
                (%s, NULL, 'worker', %s, %s, %s, NOW())
            """,
            (str(uuid.uuid4()), NAME, prefix, key_hash),
        )
finally:
    conn.close()

# stderr for human-readable announcement, stdout for machine-readable secret
print(
    f"[issue_worker_key] issued worker key (name={NAME!r}, prefix={prefix})",
    file=sys.stderr,
)
print(full)
