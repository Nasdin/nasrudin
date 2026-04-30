# Deploy

Operational notes for running the API + frontend in production.

Most of the moving pieces are documented inline in their unit / config files
(`systemd/*.service`, `Caddyfile.native`, `scripts/`). This README is for
ops decisions that don't fit cleanly anywhere else.

## GitHub OAuth (sign-in)

To enable the **"Continue with GitHub"** button on `/signin`, register a
GitHub OAuth app and wire the credentials into the API.

1. Visit <https://github.com/settings/developers> → **New OAuth App**.
2. **Application name:** Nasrudin (or per-environment, e.g. `Nasrudin (staging)`).
3. **Homepage URL:** `https://nasrudin.app` (or staging URL).
4. **Authorization callback URL:** `https://nasrudin.app/api/auth/github/callback`
   — must match `GITHUB_OAUTH_REDIRECT_URI` exactly, including scheme.
5. After creation, click **Generate a new client secret**.
6. Set in the systemd unit `Environment=` block (or `.env`):
   - `GITHUB_OAUTH_CLIENT_ID=Iv1.…`
   - `GITHUB_OAUTH_CLIENT_SECRET=<the secret>`
   - `GITHUB_OAUTH_REDIRECT_URI=https://nasrudin.app/api/auth/github/callback`

The API logs `GitHub OAuth configured` at startup when all three are set;
otherwise the routes return `503 oauth_not_configured` and the email /
password flow still works.

For local development against a non-TLS callback URL, also set:

```
OAUTH_COOKIE_SECURE=false
```

so the state cookie isn't dropped over plain HTTP.
