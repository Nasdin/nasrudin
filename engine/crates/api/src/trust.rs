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

use std::num::NonZeroUsize;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use lru::LruCache;
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
// TrustCache — `lru` crate behind a Mutex, 30 s TTL, 4096 capacity.
// ---------------------------------------------------------------------------
//
// The previous DashMap implementation used a "drop the first 16 keys we
// encounter" eviction that wasn't actually LRU and could thrash on hot
// keys under load. Switching to `LruCache` gives true recency-of-use
// eviction; the Mutex is fine here because critical sections are tiny
// (one HashMap probe + Instant compare) and the call rate is bounded by
// the worker submission rate.

#[derive(Clone)]
pub struct TrustCache {
    inner: Arc<Mutex<LruCache<Uuid, (Instant, TrustDecision)>>>,
    ttl: Duration,
}

impl TrustCache {
    pub fn new(ttl: Duration, capacity: usize) -> Self {
        // capacity = 0 would panic on the NonZeroUsize unwrap; clamp to 1.
        let cap = NonZeroUsize::new(capacity.max(1)).expect("capacity > 0");
        Self {
            inner: Arc::new(Mutex::new(LruCache::new(cap))),
            ttl,
        }
    }

    pub fn get(&self, key_id: &Uuid) -> Option<TrustDecision> {
        let mut g = self.inner.lock().ok()?;
        // `get` bumps the entry to most-recently-used. If the entry is
        // past TTL we evict and treat it as a miss so the caller refreshes
        // from PG.
        let entry = g.get(key_id)?.clone();
        if entry.0.elapsed() < self.ttl {
            Some(entry.1)
        } else {
            g.pop(key_id);
            None
        }
    }

    pub fn put(&self, key_id: Uuid, decision: TrustDecision) {
        if let Ok(mut g) = self.inner.lock() {
            g.put(key_id, (Instant::now(), decision));
        }
    }

    pub fn invalidate(&self, key_id: &Uuid) {
        if let Ok(mut g) = self.inner.lock() {
            g.pop(key_id);
        }
    }

    pub fn purge_all(&self) {
        if let Ok(mut g) = self.inner.lock() {
            g.clear();
        }
    }

    pub fn len(&self) -> usize {
        self.inner.lock().map(|g| g.len()).unwrap_or(0)
    }

    pub fn is_empty(&self) -> bool {
        self.inner.lock().map(|g| g.is_empty()).unwrap_or(true)
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
