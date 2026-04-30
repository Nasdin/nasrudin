//! Trust resolution for worker submissions (Phase admin-panel).
//!
//! Decides whether a submission from a given API key should bypass the
//! redundant server-side `lake build` confirmation, and at what
//! spot-check rate (1-in-N sampling for cascade-reject + reputation-EMA
//! verification).
//!
//! Resolution order (first match wins):
//! 1. `via_unix_socket=true` → trusted, source=UnixSocket
//! 2. `api_keys.trust_override` (Some(_)) → use that, source=ApiKeyOverride
//! 3. `users.is_trusted` → use that, source=UserFlag
//! 4. else → not trusted, source=Default
//!
//! Spot-check rate cascades through key → user → env default at every
//! step. NULL means "fall through to the next layer".

use std::sync::Arc;
use std::time::{Duration, Instant};

use dashmap::DashMap;
use nasrudin_pg::entity::{api_keys, users};
use nasrudin_pg::sea_orm::{DatabaseConnection, DbErr, EntityTrait};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum TrustSource {
    UnixSocket,
    ApiKeyOverride,
    UserFlag,
    Default,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TrustDecision {
    pub trusted: bool,
    pub spot_check_rate: u32,
    pub source: TrustSource,
}

/// Marker placed in request extensions by the unix-socket-only middleware
/// in `main.rs`. Public TCP requests cannot present this — a request that
/// lands on Caddy → 127.0.0.1:3001 never traverses the UDS layer.
#[derive(Clone, Copy, Debug)]
pub struct LocalSocket;

/// Resolve the trust decision for a worker submission.
///
/// `api_key_row` is `None` when the caller had no key (admin/system path).
/// `via_unix_socket` is `true` when the request landed on the UDS listener.
/// `env_default_rate` is the `TRUSTED_SPOT_CHECK_RATE` env value (default 50).
pub async fn resolve(
    pg: &DatabaseConnection,
    api_key_row: Option<&api_keys::Model>,
    via_unix_socket: bool,
    env_default_rate: u32,
) -> Result<TrustDecision, DbErr> {
    if via_unix_socket {
        let rate = api_key_row
            .and_then(|k| k.spot_check_rate.map(|r| r as u32))
            .unwrap_or(env_default_rate);
        return Ok(TrustDecision {
            trusted: true,
            spot_check_rate: rate,
            source: TrustSource::UnixSocket,
        });
    }

    let key = match api_key_row {
        Some(k) => k,
        None => {
            return Ok(TrustDecision {
                trusted: false,
                spot_check_rate: env_default_rate,
                source: TrustSource::Default,
            });
        }
    };

    if let Some(override_) = key.trust_override {
        let user_rate = if let Some(uid) = key.user_id {
            users::Entity::find_by_id(uid)
                .one(pg)
                .await?
                .and_then(|u| u.spot_check_rate.map(|r| r as u32))
        } else {
            None
        };
        let rate = key
            .spot_check_rate
            .map(|r| r as u32)
            .or(user_rate)
            .unwrap_or(env_default_rate);
        return Ok(TrustDecision {
            trusted: override_,
            spot_check_rate: rate,
            source: TrustSource::ApiKeyOverride,
        });
    }

    let user_id = match key.user_id {
        Some(u) => u,
        None => {
            return Ok(TrustDecision {
                trusted: false,
                spot_check_rate: env_default_rate,
                source: TrustSource::Default,
            });
        }
    };
    let user = users::Entity::find_by_id(user_id).one(pg).await?;
    let user = match user {
        Some(u) => u,
        None => {
            return Ok(TrustDecision {
                trusted: false,
                spot_check_rate: env_default_rate,
                source: TrustSource::Default,
            });
        }
    };

    if user.is_trusted {
        let rate = key
            .spot_check_rate
            .map(|r| r as u32)
            .or(user.spot_check_rate.map(|r| r as u32))
            .unwrap_or(env_default_rate);
        return Ok(TrustDecision {
            trusted: true,
            spot_check_rate: rate,
            source: TrustSource::UserFlag,
        });
    }

    Ok(TrustDecision {
        trusted: false,
        spot_check_rate: env_default_rate,
        source: TrustSource::Default,
    })
}

/// FNV-1a 64-bit. Deterministic per-theorem hash for stable spot-check
/// sampling — re-running the drain picks the same sampled subset
/// (predictable forensics, no replay flakiness).
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Decision: should this theorem be promoted to the lake-promotion drain?
///
/// - Untrusted decisions always promote (full kernel confirmation).
/// - `spot_check_rate == 0` → pure trust, never promote.
/// - `spot_check_rate == 1` → effectively untrusted, always promote.
/// - Otherwise: 1-in-N sampling, deterministic per theorem id.
pub fn should_promote(decision: &TrustDecision, theorem_id: &[u8]) -> bool {
    if !decision.trusted {
        return true;
    }
    match decision.spot_check_rate {
        0 => false,
        1 => true,
        n => fnv1a64(theorem_id) % (n as u64) == 0,
    }
}

// ---------------------------------------------------------------------------
// TrustCache — dashmap-backed, 30 s TTL, 4096 capacity (rough LRU).
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct TrustCache {
    inner: Arc<DashMap<Uuid, (Instant, TrustDecision)>>,
    ttl: Duration,
    capacity: usize,
}

impl TrustCache {
    pub fn new(ttl: Duration, capacity: usize) -> Self {
        Self {
            inner: Arc::new(DashMap::with_capacity(capacity)),
            ttl,
            capacity,
        }
    }

    pub fn get(&self, key_id: &Uuid) -> Option<TrustDecision> {
        let entry = self.inner.get(key_id)?;
        let (when, ref dec) = *entry;
        if when.elapsed() < self.ttl {
            Some(dec.clone())
        } else {
            None
        }
    }

    pub fn put(&self, key_id: Uuid, decision: TrustDecision) {
        if self.inner.len() >= self.capacity {
            // Cheap eviction: drop the first 16 entries we encounter.
            // The TTL still prunes stale entries naturally on get(), so
            // this just bounds memory.
            let mut evicted = 0;
            self.inner.retain(|_, _| {
                evicted += 1;
                evicted > 16
            });
        }
        self.inner.insert(key_id, (Instant::now(), decision));
    }

    pub fn invalidate(&self, key_id: &Uuid) {
        self.inner.remove(key_id);
    }

    pub fn purge_all(&self) {
        self.inner.clear();
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

#[derive(Clone, Debug)]
pub enum CacheInvalidation {
    ApiKey(Uuid),
    User(Uuid),
    All,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fnv1a64_deterministic() {
        assert_eq!(fnv1a64(b"abc"), fnv1a64(b"abc"));
        assert_ne!(fnv1a64(b"abc"), fnv1a64(b"abd"));
    }

    #[test]
    fn untrusted_always_promotes() {
        let d = TrustDecision {
            trusted: false,
            spot_check_rate: 1000,
            source: TrustSource::Default,
        };
        for i in 0..100u64 {
            assert!(should_promote(&d, &i.to_le_bytes()));
        }
    }

    #[test]
    fn trusted_rate_zero_never_promotes() {
        let d = TrustDecision {
            trusted: true,
            spot_check_rate: 0,
            source: TrustSource::UserFlag,
        };
        for i in 0..100u64 {
            assert!(!should_promote(&d, &i.to_le_bytes()));
        }
    }

    #[test]
    fn trusted_rate_one_always_promotes() {
        let d = TrustDecision {
            trusted: true,
            spot_check_rate: 1,
            source: TrustSource::UserFlag,
        };
        for i in 0..100u64 {
            assert!(should_promote(&d, &i.to_le_bytes()));
        }
    }

    #[test]
    fn cache_round_trip_and_invalidate() {
        let cache = TrustCache::new(Duration::from_secs(30), 16);
        let id = Uuid::new_v4();
        let dec = TrustDecision {
            trusted: true,
            spot_check_rate: 50,
            source: TrustSource::UserFlag,
        };
        cache.put(id, dec.clone());
        assert!(cache.get(&id).is_some());
        cache.invalidate(&id);
        assert!(cache.get(&id).is_none());
    }

    #[test]
    fn cache_capacity_bounds_size() {
        let cache = TrustCache::new(Duration::from_secs(30), 4);
        for _ in 0..10 {
            cache.put(
                Uuid::new_v4(),
                TrustDecision {
                    trusted: false,
                    spot_check_rate: 50,
                    source: TrustSource::Default,
                },
            );
        }
        assert!(cache.len() <= 4);
    }
}
