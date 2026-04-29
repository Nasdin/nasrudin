//! Stripe webhook signature verification + minimal event parsing.
//!
//! Stripe signs every webhook payload with HMAC-SHA256 over
//! `<timestamp>.<raw_body>`, included in the `Stripe-Signature` header
//! as `t=<unix>,v1=<hex>` (and possibly other `vN` schemes). We verify
//! the v1 signature with constant-time compare and parse just the
//! fields we care about — no need to deserialize Stripe's full type
//! tree for what amounts to four event types.

use hmac::{Hmac, Mac};
use serde::Deserialize;
use sha2::Sha256;
use subtle::ConstantTimeEq;

use crate::billing::stripe_client::BillingConfig;
use crate::billing::tier::PlanTier;

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    InvalidUtf8,
    InvalidSignature,
    InvalidJson,
    MalformedHeader,
    SignatureMismatch,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for ParseError {}

#[derive(Debug, Deserialize)]
pub struct StripeEvent {
    pub id: String,
    #[serde(rename = "type")]
    pub event_type: String,
    pub data: StripeData,
}

#[derive(Debug, Deserialize)]
pub struct StripeData {
    /// `object` is the resource (`subscription`, `invoice`, …). We only
    /// pluck the fields we need so a Stripe API addition doesn't break
    /// deserialization.
    pub object: serde_json::Value,
}

pub struct WebhookProcessor {
    pub secret: String,
}

impl WebhookProcessor {
    /// Verify the `Stripe-Signature` header against `payload`. Returns
    /// the parsed event on success.
    pub fn parse_event(
        &self,
        payload: &[u8],
        sig_header: &str,
    ) -> Result<StripeEvent, ParseError> {
        let (timestamp, signatures) = parse_sig_header(sig_header)?;
        let signed = format!(
            "{timestamp}.{}",
            std::str::from_utf8(payload).map_err(|_| ParseError::InvalidUtf8)?
        );
        let mut mac = <Hmac<Sha256> as Mac>::new_from_slice(self.secret.as_bytes())
            .map_err(|_| ParseError::InvalidSignature)?;
        mac.update(signed.as_bytes());
        let expected = mac.finalize().into_bytes();
        let expected_hex = hex::encode(expected);

        // Constant-time compare against any provided v1 signature.
        let any_match = signatures.iter().any(|s| {
            s.len() == expected_hex.len()
                && s.as_bytes().ct_eq(expected_hex.as_bytes()).into()
        });
        if !any_match {
            return Err(ParseError::SignatureMismatch);
        }

        serde_json::from_slice(payload).map_err(|_| ParseError::InvalidJson)
    }
}

/// Parse the comma-separated `Stripe-Signature` header. Returns
/// `(timestamp, [v1_signatures...])`. Stripe rotates secrets by emitting
/// multiple `v1=` entries during the rotation window.
fn parse_sig_header(header: &str) -> Result<(&str, Vec<&str>), ParseError> {
    let mut timestamp: Option<&str> = None;
    let mut sigs: Vec<&str> = Vec::new();
    for part in header.split(',') {
        let mut it = part.splitn(2, '=');
        let k = it.next().unwrap_or("").trim();
        let v = it.next().unwrap_or("").trim();
        match k {
            "t" => timestamp = Some(v),
            "v1" => sigs.push(v),
            _ => {}
        }
    }
    let t = timestamp.ok_or(ParseError::MalformedHeader)?;
    if sigs.is_empty() {
        return Err(ParseError::MalformedHeader);
    }
    Ok((t, sigs))
}

/// Phase-1 price→tier map. Researcher is the only paid tier with
/// self-serve checkout right now; Team/Institution flow through a
/// sales-contact CTA and ship in a separate plan.
pub fn tier_for_price(price_id: &str, cfg: &BillingConfig) -> PlanTier {
    if price_id == cfg.price_researcher_monthly || price_id == cfg.price_researcher_annual {
        PlanTier::Researcher
    } else {
        PlanTier::Free
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sign(secret: &str, timestamp: &str, payload: &str) -> String {
        let signed = format!("{timestamp}.{payload}");
        let mut mac = <Hmac<Sha256> as Mac>::new_from_slice(secret.as_bytes()).unwrap();
        mac.update(signed.as_bytes());
        hex::encode(mac.finalize().into_bytes())
    }

    #[test]
    fn rejects_invalid_signature() {
        let p = WebhookProcessor {
            secret: "whsec_test".into(),
        };
        let result = p.parse_event(b"{}", "t=1700000000,v1=garbage");
        assert!(matches!(
            result,
            Err(ParseError::SignatureMismatch | ParseError::InvalidJson)
        ));
    }

    #[test]
    fn rejects_missing_v1() {
        let p = WebhookProcessor {
            secret: "whsec_test".into(),
        };
        let result = p.parse_event(b"{}", "t=1700000000");
        assert_eq!(result.unwrap_err(), ParseError::MalformedHeader);
    }

    #[test]
    fn accepts_well_formed_signature_and_parses() {
        let secret = "whsec_test";
        let payload = r#"{"id":"evt_123","type":"customer.subscription.created","data":{"object":{"id":"sub_1"}}}"#;
        let timestamp = "1700000000";
        let sig = sign(secret, timestamp, payload);
        let header = format!("t={timestamp},v1={sig}");
        let p = WebhookProcessor {
            secret: secret.into(),
        };
        let event = p.parse_event(payload.as_bytes(), &header).unwrap();
        assert_eq!(event.id, "evt_123");
        assert_eq!(event.event_type, "customer.subscription.created");
    }

    #[test]
    fn rotation_window_accepts_either_v1() {
        let secret = "whsec_test";
        let payload = r#"{"id":"evt_x","type":"foo","data":{"object":{}}}"#;
        let timestamp = "1700000000";
        let good = sign(secret, timestamp, payload);
        let header = format!("t={timestamp},v1=deadbeef,v1={good}");
        let p = WebhookProcessor {
            secret: secret.into(),
        };
        assert!(p.parse_event(payload.as_bytes(), &header).is_ok());
    }
}
