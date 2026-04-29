//! Long-lived `lean --run nasrudin_server.lean` client.
//!
//! Spawns one subprocess that imports Mathlib at boot, then multiplexes
//! requests through a tokio mpsc channel. Responses are correlated by
//! `id` field — see `persistent_protocol.rs`.
//!
//! The Lean-side script is a stub today (only `Ping` is implemented).
//! `Elaborate` / `VerifyTactic` requests will receive a `Fatal` response,
//! and callers should fall back to the existing process-per-call path.
//! The full Lean implementation is owned by the prover team.

use crate::persistent_protocol::{Request, Response};
use anyhow::{Context, Result, anyhow};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::Command;
use tokio::sync::{Mutex, mpsc, oneshot};

/// Configuration for [`PersistentElaborator`].
#[derive(Debug, Clone)]
pub struct PersistentElaboratorConfig {
    /// Path to `nasrudin_server.lean` (relative to `cwd`).
    pub script_path: PathBuf,
    /// Working directory the `lean` process runs in (typically `prover/`).
    pub cwd: PathBuf,
    /// How long to wait for the initial Mathlib-loaded ack on stdout.
    pub boot_timeout: Duration,
    /// Per-request timeout from `send` to response receipt.
    pub request_timeout: Duration,
}

impl Default for PersistentElaboratorConfig {
    fn default() -> Self {
        Self {
            script_path: PathBuf::from("scripts/nasrudin_server.lean"),
            cwd: PathBuf::from("../prover"),
            boot_timeout: Duration::from_secs(30),
            request_timeout: Duration::from_secs(30),
        }
    }
}

impl PersistentElaboratorConfig {
    /// Read overrides from env (`NASRUDIN_LEAN_SCRIPT`, `NASRUDIN_PROVER_ROOT`).
    pub fn from_env() -> Self {
        let mut cfg = Self::default();
        if let Ok(s) = std::env::var("NASRUDIN_LEAN_SCRIPT") {
            cfg.script_path = PathBuf::from(s);
        }
        if let Ok(s) = std::env::var("NASRUDIN_PROVER_ROOT") {
            cfg.cwd = PathBuf::from(s);
        }
        cfg
    }
}

type Inflight = Arc<Mutex<HashMap<u64, oneshot::Sender<Response>>>>;

/// A handle to a long-lived `lean --run` subprocess.
///
/// Construction is `async` because we wait for the boot ack before
/// returning. Drop kills the subprocess (via the supervisor task on the
/// other end of the mpsc channel).
pub struct PersistentElaborator {
    next_id: AtomicU64,
    tx: mpsc::Sender<(Request, Option<oneshot::Sender<Response>>)>,
    request_timeout: Duration,
    /// Kept so the supervisor task is dropped when the handle is.
    _supervisor: tokio::task::JoinHandle<()>,
}

impl PersistentElaborator {
    /// Spawn `lean --run <script>` and wait for the boot ack.
    pub async fn new(cfg: PersistentElaboratorConfig) -> Result<Self> {
        let mut child = Command::new("lean")
            .arg("--run")
            .arg(&cfg.script_path)
            .current_dir(&cfg.cwd)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .context("spawn lean --run")?;

        let stdin = child.stdin.take().context("take stdin")?;
        let stdout = child.stdout.take().context("take stdout")?;
        let mut reader = BufReader::new(stdout).lines();

        // Wait for `{"kind":"ok","id":0}` boot ack.
        let boot = tokio::time::timeout(cfg.boot_timeout, reader.next_line())
            .await
            .map_err(|_| anyhow!("boot ack timed out after {:?}", cfg.boot_timeout))?
            .context("read boot ack line")?
            .ok_or_else(|| anyhow!("server closed stdout before boot ack"))?;
        let parsed: Response =
            serde_json::from_str(&boot).context("parse boot ack")?;
        match parsed {
            Response::Ok { id: 0 } => {}
            other => {
                return Err(anyhow!("unexpected boot response: {other:?}"));
            }
        }

        let (tx, mut rx) =
            mpsc::channel::<(Request, Option<oneshot::Sender<Response>>)>(64);
        let inflight: Inflight = Arc::new(Mutex::new(HashMap::new()));

        // Reader task: parse each line as a Response, route to its oneshot.
        let inflight_r = inflight.clone();
        tokio::spawn(async move {
            while let Ok(Some(line)) = reader.next_line().await {
                let resp: Response = match serde_json::from_str(&line) {
                    Ok(r) => r,
                    Err(e) => {
                        tracing::warn!("persistent lean: bad response line: {e}; raw={line}");
                        continue;
                    }
                };
                if let Some(id) = response_id(&resp) {
                    let mut g = inflight_r.lock().await;
                    if let Some(sender) = g.remove(&id) {
                        // Receiver may have dropped; ignore send errors.
                        let _ = sender.send(resp);
                    }
                } else if let Response::Fatal { message } = resp {
                    tracing::error!("persistent lean fatal: {message}");
                    drain_inflight_with_fatal(&inflight_r, &message).await;
                }
            }
        });

        // Writer / supervisor task: pull requests off rx, write to stdin,
        // register oneshot. Kills the child when the channel closes.
        let inflight_w = inflight.clone();
        let supervisor = tokio::spawn(async move {
            let mut stdin = stdin;
            while let Some((req, oneshot_tx)) = rx.recv().await {
                if let (Some(id), Some(sender)) = (request_id(&req), oneshot_tx) {
                    inflight_w.lock().await.insert(id, sender);
                }
                let mut line = match serde_json::to_vec(&req) {
                    Ok(b) => b,
                    Err(e) => {
                        tracing::error!("serialise request: {e}");
                        continue;
                    }
                };
                line.push(b'\n');
                if stdin.write_all(&line).await.is_err() {
                    break;
                }
                if stdin.flush().await.is_err() {
                    break;
                }
            }
            let _ = child.kill().await;
        });

        Ok(Self {
            next_id: AtomicU64::new(1),
            tx,
            request_timeout: cfg.request_timeout,
            _supervisor: supervisor,
        })
    }

    /// Health check.
    pub async fn ping(&self) -> Result<()> {
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        let _ = self.send(Request::Ping { id }).await?;
        Ok(())
    }

    /// Type-check a Lean source. Returns the elaborator's response.
    ///
    /// Today the stub script answers `Fatal` for this; callers should
    /// fall back to the process-per-call path.
    pub async fn elaborate(&self, source: &str) -> Result<Response> {
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        self.send(Request::Elaborate {
            id,
            source: source.to_string(),
        })
        .await
    }

    /// Verify a tactic against the goal in `source`.
    pub async fn verify_tactic(&self, source: &str, tactic: &str) -> Result<Response> {
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        self.send(Request::VerifyTactic {
            id,
            source: source.to_string(),
            tactic: tactic.to_string(),
        })
        .await
    }

    /// Send Shutdown and consume the elaborator handle. Best-effort —
    /// the supervisor will also kill the child on Drop if Shutdown is
    /// not sent.
    pub async fn shutdown(self) -> Result<()> {
        let _ = self.tx.send((Request::Shutdown, None)).await;
        Ok(())
    }

    async fn send(&self, req: Request) -> Result<Response> {
        let (resp_tx, resp_rx) = oneshot::channel();
        self.tx
            .send((req, Some(resp_tx)))
            .await
            .map_err(|_| anyhow!("server gone"))?;
        let resp = tokio::time::timeout(self.request_timeout, resp_rx)
            .await
            .map_err(|_| anyhow!("request timeout after {:?}", self.request_timeout))?
            .map_err(|_| anyhow!("response channel dropped"))?;
        Ok(resp)
    }
}

fn request_id(req: &Request) -> Option<u64> {
    match req {
        Request::Elaborate { id, .. }
        | Request::VerifyTactic { id, .. }
        | Request::Ping { id } => Some(*id),
        Request::Shutdown => None,
    }
}

fn response_id(resp: &Response) -> Option<u64> {
    match resp {
        Response::Ok { id }
        | Response::ElaborateOk { id, .. }
        | Response::ElaborateError { id, .. }
        | Response::VerifyOk { id, .. }
        | Response::VerifyError { id, .. }
        | Response::Pong { id } => Some(*id),
        Response::Fatal { .. } => None,
    }
}

/// Drain every pending oneshot in `inflight` and signal each one with a
/// `Response::Fatal { message }`. Called when the elaborator emits a
/// non-correlated `Fatal` so callers fail fast instead of waiting for
/// the per-request timeout.
async fn drain_inflight_with_fatal(inflight: &Inflight, message: &str) {
    let mut g = inflight.lock().await;
    let drained: Vec<oneshot::Sender<Response>> = g.drain().map(|(_, s)| s).collect();
    drop(g);
    for sender in drained {
        let _ = sender.send(Response::Fatal {
            message: message.to_string(),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn config_default_points_at_prover_root() {
        let cfg = PersistentElaboratorConfig::default();
        assert!(cfg.script_path.ends_with("nasrudin_server.lean"));
        assert!(cfg.cwd.ends_with("prover"));
        assert!(cfg.boot_timeout >= Duration::from_secs(1));
        assert!(cfg.request_timeout >= Duration::from_secs(1));
    }

    #[tokio::test]
    async fn config_from_env_overrides_paths() {
        let _g_script = EnvGuard::set("NASRUDIN_LEAN_SCRIPT", "/tmp/test_script.lean");
        let _g_root = EnvGuard::set("NASRUDIN_PROVER_ROOT", "/tmp/test_prover");
        let cfg = PersistentElaboratorConfig::from_env();
        assert_eq!(cfg.script_path, PathBuf::from("/tmp/test_script.lean"));
        assert_eq!(cfg.cwd, PathBuf::from("/tmp/test_prover"));
    }

    #[test]
    fn request_id_extraction() {
        assert_eq!(
            request_id(&Request::Ping { id: 7 }),
            Some(7)
        );
        assert_eq!(
            request_id(&Request::Elaborate {
                id: 11,
                source: "".into()
            }),
            Some(11)
        );
        assert_eq!(request_id(&Request::Shutdown), None);
    }

    /// Synthetic test: directly invoke the inflight-drain helper with a
    /// populated map, confirm every oneshot fires with a Fatal payload
    /// (mirroring what the reader task does on Fatal).
    #[tokio::test]
    async fn fatal_drains_inflight_oneshots() {
        let inflight: Inflight = Arc::new(Mutex::new(HashMap::new()));
        let (tx_a, rx_a) = oneshot::channel::<Response>();
        let (tx_b, rx_b) = oneshot::channel::<Response>();
        {
            let mut g = inflight.lock().await;
            g.insert(1, tx_a);
            g.insert(2, tx_b);
        }
        drain_inflight_with_fatal(&inflight, "lean process exploded").await;
        let r_a = rx_a.await.expect("oneshot A should fire");
        let r_b = rx_b.await.expect("oneshot B should fire");
        assert!(matches!(r_a, Response::Fatal { .. }));
        assert!(matches!(r_b, Response::Fatal { .. }));
        assert!(inflight.lock().await.is_empty());
    }

    #[test]
    fn response_id_extraction() {
        assert_eq!(
            response_id(&Response::Ok { id: 0 }),
            Some(0)
        );
        assert_eq!(
            response_id(&Response::Pong { id: 5 }),
            Some(5)
        );
        assert_eq!(
            response_id(&Response::Fatal {
                message: "x".into()
            }),
            None
        );
    }

    /// Save and restore env across one test.
    struct EnvGuard {
        key: String,
        prev: Option<String>,
    }
    impl EnvGuard {
        fn set(key: &str, val: &str) -> Self {
            let prev = std::env::var(key).ok();
            // SAFETY: tests in this module use disjoint env keys.
            unsafe {
                std::env::set_var(key, val);
            }
            Self {
                key: key.to_string(),
                prev,
            }
        }
    }
    impl Drop for EnvGuard {
        fn drop(&mut self) {
            unsafe {
                match &self.prev {
                    Some(v) => std::env::set_var(&self.key, v),
                    None => std::env::remove_var(&self.key),
                }
            }
        }
    }
}
