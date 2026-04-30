//! GitHub OAuth handlers — authorization-code flow on top of axum-login.
//!
//! See spec at
//! `docs/superpowers/specs/2026-04-30-real-signin-and-github-oauth-design.md`.
//!
//! Endpoints (filled in by Tasks 9 + 10):
//!   - `GET /api/auth/github/start`    — issue state, redirect to github.com
//!   - `GET /api/auth/github/callback` — verify state, exchange code, sign in
