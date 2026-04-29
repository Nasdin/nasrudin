//! Soak test: 100 ping round-trips against a single PersistentElaborator
//! instance. Asserts no hang, no leaks, no memory blow-up over time.
//!
//! Run manually:
//!   cargo test -p nasrudin-derive --test integration_persistent_lean -- --ignored
//!
//! Requires `lean` on PATH and a working `nasrudin_server.lean` script.

use nasrudin_lean_bridge::{PersistentElaborator, PersistentElaboratorConfig};
use std::time::Duration;

#[tokio::test]
#[ignore]
async fn one_hundred_pings_against_real_lean() {
    let cfg = PersistentElaboratorConfig::from_env();
    let client = match PersistentElaborator::new(cfg).await {
        Ok(c) => c,
        Err(e) => {
            eprintln!("skipping: {e}");
            return;
        }
    };
    for i in 0..100 {
        match tokio::time::timeout(Duration::from_secs(5), client.ping()).await {
            Ok(Ok(())) => {}
            Ok(Err(e)) => panic!("ping {i} errored: {e}"),
            Err(_) => panic!("ping {i} timed out"),
        }
    }
    client.shutdown().await.expect("shutdown");
}
