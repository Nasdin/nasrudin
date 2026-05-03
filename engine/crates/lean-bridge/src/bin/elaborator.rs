//! Long-lived Lean elaborator daemon — owns one `lake env lean --run`
//! child process and exposes its JSON-line protocol over a unix-domain
//! socket.
//!
//! On a 2 GB droplet the worker OOMs every 10-15 min and gets restarted
//! by systemd. If the Lean child is parented by the worker, every restart
//! pays the 15+ minute Mathlib import again — and we never produce a
//! theorem. With this daemon the boot cost is paid once per day; worker
//! reconnects in <100 ms.
//!
//! Wire protocol matches `crate::persistent_protocol`. The daemon is
//! transparent: it does not parse or rewrite request IDs. Clients pick
//! their own IDs, and the daemon serialises every (write_request →
//! read_response) pair under one mutex so there is no cross-client
//! interleaving.

use anyhow::{Context, Result, anyhow};
use nasrudin_lean_bridge::{
    PersistentElaboratorConfig,
    persistent_protocol::{Request, Response},
};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::net::{UnixListener, UnixStream};
use tokio::process::{ChildStdin, ChildStdout, Command};
use tokio::sync::Mutex;

/// All client traffic flows through this single mutex-guarded pair so
/// requests can never interleave. Lean processes one request at a time,
/// matching this serialisation exactly.
struct LeanIo {
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    let socket_path = std::env::var("NASRUDIN_ELAB_UDS")
        .unwrap_or_else(|_| "/run/nasrudin/elab.sock".to_string());
    let socket_path = PathBuf::from(socket_path);

    // Spawn Lean — re-uses PersistentElaboratorConfig so all the
    // NASRUDIN_LEAN_* env knobs (boot timeout, prover root, script path)
    // behave exactly as in the in-process path.
    let cfg = PersistentElaboratorConfig::from_env();
    tracing::info!(
        cwd = %cfg.cwd.display(),
        script = %cfg.script_path.display(),
        boot_timeout_secs = cfg.boot_timeout.as_secs(),
        "spawning lake env lean --run"
    );

    let mut cmd = Command::new("lake");
    if let Some(home) = std::env::var_os("HOME") {
        let elan_bin = std::path::PathBuf::from(home).join(".elan/bin");
        if elan_bin.exists() {
            let current_path = std::env::var_os("PATH").unwrap_or_default();
            let mut new_path = std::ffi::OsString::from(&elan_bin);
            new_path.push(":");
            new_path.push(&current_path);
            cmd.env("PATH", new_path);
        }
    }
    let mut child = cmd
        .arg("env")
        .arg("lean")
        .arg("--run")
        .arg(&cfg.script_path)
        .current_dir(&cfg.cwd)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .context("spawn lake env lean --run")?;

    let stdin = child.stdin.take().context("take stdin")?;
    let stdout = child.stdout.take().context("take stdout")?;
    let mut stdout = BufReader::new(stdout);

    // Drain stderr in the background so it doesn't block the child if
    // Lean logs heavily.
    if let Some(stderr) = child.stderr.take() {
        tokio::spawn(async move {
            let mut s = stderr;
            let mut buf = [0u8; 8192];
            while let Ok(n) = s.read(&mut buf).await {
                if n == 0 {
                    break;
                }
                tracing::debug!(
                    "lean stderr: {}",
                    String::from_utf8_lossy(&buf[..n]).trim_end()
                );
            }
        });
    }

    // Wait for boot ack — `{"kind":"ok","id":0}` — before we open the
    // listener. Clients connecting before this point would see EOF.
    tracing::info!("waiting for Lean boot ack (Mathlib import)…");
    let mut boot_line = String::new();
    let read = tokio::time::timeout(
        cfg.boot_timeout,
        stdout.read_line(&mut boot_line),
    )
    .await
    .map_err(|_| {
        anyhow!(
            "boot ack timed out after {:?} — increase NASRUDIN_LEAN_BOOT_TIMEOUT_SECS",
            cfg.boot_timeout
        )
    })?
    .context("read boot ack line")?;
    if read == 0 {
        return Err(anyhow!("lean closed stdout before boot ack"));
    }
    let boot_ack_raw = boot_line.trim().to_string();
    // Critical: the *first* line on stdout is sometimes Lean's compiler
    // complaining about a missing import (e.g. "unknown module prefix
    // 'PhysicsGenerator'") rather than the script's own
    // {"kind":"ok","id":0} ack. Without parsing it we'd happily start
    // listening on a dead Lean child. Parse strictly and fail loudly so
    // systemd loops us until the operator sees the journal and fixes
    // the actual problem (typically: `lake build` the local package
    // before starting this daemon).
    let parsed: Response = serde_json::from_str(&boot_ack_raw).map_err(|e| {
        anyhow!(
            "boot ack is not valid JSON ({e}); raw line: {boot_ack_raw}\n\
             this usually means `lake env lean --run` failed to import\n\
             a module before reaching the script's IO.println — run\n\
             `cd $NASRUDIN_PROVER_ROOT && lake build` and check stderr."
        )
    })?;
    match parsed {
        Response::Ok { id: 0 } => {}
        other => {
            return Err(anyhow!(
                "unexpected boot response: {other:?}; raw: {boot_ack_raw}"
            ));
        }
    }
    tracing::info!(boot_ack = %boot_ack_raw, "Lean is hot");

    // Bind UDS. Remove a stale socket file from a previous unclean shutdown.
    if socket_path.exists() {
        std::fs::remove_file(&socket_path).context("remove stale socket file")?;
    }
    if let Some(parent) = socket_path.parent() {
        std::fs::create_dir_all(parent).ok();
    }
    let listener = UnixListener::bind(&socket_path)
        .with_context(|| format!("bind {}", socket_path.display()))?;

    // 0660 + nasrudin:nasrudin → only group members can connect. Same
    // pattern as /run/nasrudin/api-local.sock. Worker runs as nasrudin
    // so it's in the group.
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&socket_path, std::fs::Permissions::from_mode(0o660))
        .context("set socket permissions to 0660")?;
    tracing::info!(socket = %socket_path.display(), "elaborator listening");

    let io = Arc::new(Mutex::new(LeanIo { stdin, stdout }));

    // Health check: send a Ping ourselves and verify the elaborator
    // responds. Surfaces a hung Lean *before* clients connect so systemd
    // restarts us cleanly instead of accepting connections that hang.
    {
        let mut g = io.lock().await;
        let ping = serde_json::to_vec(&Request::Ping { id: 0 })?;
        g.stdin.write_all(&ping).await?;
        g.stdin.write_all(b"\n").await?;
        g.stdin.flush().await?;
        let mut pong = String::new();
        let n = tokio::time::timeout(Duration::from_secs(30), g.stdout.read_line(&mut pong))
            .await
            .map_err(|_| anyhow!("self-ping timed out"))??;
        if n == 0 {
            return Err(anyhow!("lean closed stdout during self-ping"));
        }
        tracing::info!(pong = pong.trim(), "self-ping ok");
    }

    // Main accept loop.
    loop {
        let (stream, _addr) = listener
            .accept()
            .await
            .context("accept elaborator client")?;
        let io = Arc::clone(&io);
        tokio::spawn(async move {
            if let Err(e) = handle_client(stream, io).await {
                tracing::warn!(error=%e, "client task ended");
            }
        });
    }
}

/// Handle one client connection. Read JSON lines from the client; for
/// each, lock the Lean IO, forward, await the matching response line,
/// and write it back. The mutex ensures one (request, response) pair
/// occupies the Lean child at a time; without it, two concurrent
/// requests could interleave their stdout responses.
async fn handle_client(stream: UnixStream, io: Arc<Mutex<LeanIo>>) -> Result<()> {
    let (read_half, mut write_half) = stream.into_split();
    let mut client_lines = BufReader::new(read_half).lines();

    while let Some(line) = client_lines.next_line().await? {
        // Per-request critical section: hold the Lean IO mutex from
        // write through read. If the client disconnects mid-await,
        // we still drain the response (handler keeps running until
        // the read completes), keeping Lean's state coherent for the
        // next request.
        let response_line: String = {
            let mut g = io.lock().await;
            g.stdin.write_all(line.as_bytes()).await?;
            g.stdin.write_all(b"\n").await?;
            g.stdin.flush().await?;
            let mut resp = String::new();
            let n = g.stdout.read_line(&mut resp).await?;
            if n == 0 {
                return Err(anyhow!("lean stdout EOF — child exited"));
            }
            resp
        };
        if write_half.write_all(response_line.as_bytes()).await.is_err() {
            // Client disconnected after we already drained the
            // response; nothing more to do for this connection.
            break;
        }
        if write_half.flush().await.is_err() {
            break;
        }
    }
    Ok(())
}
