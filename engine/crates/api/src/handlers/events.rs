//! SSE event streams.
//!
//! Phase 9 / Task 5.2. The `/api/events/discoveries` stream multiplexes two
//! independent broadcast channels into a single Server-Sent-Events feed:
//!
//! 1. The GA-internal channel (`AppState::discovery_tx`) carrying
//!    [`nasrudin_ga::DiscoveryEvent`]. These ride out as `ga_discovery` events
//!    on the wire (back-compat with existing GA channel consumers).
//!
//! 2. The reverify-side channel (`AppState::reverify_event_tx`) carrying
//!    [`crate::reverify::DiscoveryEvent`]. These ride out as named events
//!    (`theorem_pending`, `theorem_verified`, `theorem_rejected`) keyed by
//!    enum variant.
//!
//! `/api/events/stats` is a 5-second-tick stream of `GaStatusSnapshot`s.
//! Phase 6.1 will fold worker_heartbeat events in here.
//!
//! Both streams emit a 15-second keep-alive ping so reverse proxies don't
//! kill idle connections.

use std::{convert::Infallible, sync::Arc, time::Duration};

use axum::{
    extract::State,
    response::sse::{Event, KeepAlive, Sse},
};
use tokio_stream::{Stream, StreamExt, wrappers::BroadcastStream};

use crate::reverify::DiscoveryEvent as ReverifyEvent;
use crate::state::AppState;

/// Multiplexed discovery stream: emits both GA-internal `ga_discovery` events
/// and reverify-side `theorem_pending` / `theorem_verified` /
/// `theorem_rejected` events on a single SSE connection.
pub async fn discoveries(
    State(state): State<Arc<AppState>>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let rx_reverify = state.reverify_event_tx.subscribe();
    let rx_ga = state.discovery_tx.subscribe();

    let reverify_stream = BroadcastStream::new(rx_reverify).filter_map(|res| {
        let evt = res.ok()?;
        let name = match &evt {
            ReverifyEvent::TheoremPending { .. } => "theorem_pending",
            ReverifyEvent::TheoremVerified { .. } => "theorem_verified",
            ReverifyEvent::TheoremRejected { .. } => "theorem_rejected",
        };
        let data = serde_json::to_string(&evt).ok()?;
        Some(Ok(Event::default().event(name).data(data)))
    });

    let ga_stream = BroadcastStream::new(rx_ga).filter_map(|res| {
        let evt = res.ok()?;
        let data = serde_json::to_string(&evt).ok()?;
        Some(Ok(Event::default().event("ga_discovery").data(data)))
    });

    let merged = reverify_stream.merge(ga_stream);
    Sse::new(merged).keep_alive(
        KeepAlive::new()
            .interval(Duration::from_secs(15))
            .text("ping"),
    )
}

/// Live GA status stream. Emits a `ga_status_tick` event every 5 seconds
/// with the current [`nasrudin_ga::GaStatusSnapshot`] payload.
///
/// Worker heartbeat events will be folded in here in Phase 6.1.
pub async fn stats(
    State(state): State<Arc<AppState>>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let interval = tokio::time::interval(Duration::from_secs(5));
    let stream = tokio_stream::wrappers::IntervalStream::new(interval).map(move |_| {
        let snapshot = state
            .ga_status
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone();
        let data = serde_json::to_string(&snapshot).unwrap_or_default();
        Ok(Event::default().event("ga_status_tick").data(data))
    });
    Sse::new(stream).keep_alive(
        KeepAlive::new()
            .interval(Duration::from_secs(15))
            .text("ping"),
    )
}
