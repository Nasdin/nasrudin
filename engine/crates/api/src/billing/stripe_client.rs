//! Thin HTTP client for the three Stripe endpoints we use:
//! Create Customer, Create Checkout Session, Create Billing Portal Session.
//!
//! Deliberately not using async-stripe — Stripe's REST surface is stable
//! (form-encoded POST, JSON response) and a 200-line wrapper insulates
//! us from upstream SDK churn. Webhook handling lives in `webhook.rs`.

use std::sync::Arc;

use serde::Deserialize;

#[derive(Clone)]
pub struct BillingConfig {
    pub price_researcher_monthly: String,
    pub price_researcher_annual: String,
    pub checkout_success_url: String,
    pub checkout_cancel_url: String,
    pub portal_return_url: String,
    pub webhook_secret: String,
}

#[derive(Clone)]
pub struct BillingClient {
    pub http: reqwest::Client,
    pub secret_key: String,
    pub cfg: Arc<BillingConfig>,
}

const STRIPE_API: &str = "https://api.stripe.com/v1";

#[derive(Debug, thiserror::Error)]
pub enum StripeError {
    #[error("http error: {0}")]
    Http(#[from] reqwest::Error),
    #[error("stripe returned {status}: {body}")]
    Api { status: u16, body: String },
    #[error("missing field in stripe response: {0}")]
    MissingField(&'static str),
}

#[derive(Deserialize)]
struct CustomerResp {
    id: String,
}

#[derive(Deserialize)]
struct SessionResp {
    url: Option<String>,
}

impl BillingClient {
    pub fn from_env() -> anyhow::Result<Self> {
        let secret_key = std::env::var("STRIPE_SECRET_KEY")
            .map_err(|_| anyhow::anyhow!("STRIPE_SECRET_KEY not set"))?;
        let cfg = BillingConfig {
            price_researcher_monthly: std::env::var("STRIPE_PRICE_RESEARCHER_MONTHLY")?,
            price_researcher_annual: std::env::var("STRIPE_PRICE_RESEARCHER_ANNUAL")?,
            checkout_success_url: std::env::var("STRIPE_CHECKOUT_SUCCESS_URL")?,
            checkout_cancel_url: std::env::var("STRIPE_CHECKOUT_CANCEL_URL")?,
            portal_return_url: std::env::var("STRIPE_CUSTOMER_PORTAL_RETURN_URL")?,
            webhook_secret: std::env::var("STRIPE_WEBHOOK_SECRET")?,
        };
        Ok(Self {
            http: reqwest::Client::new(),
            secret_key,
            cfg: Arc::new(cfg),
        })
    }

    async fn post_form<T: for<'de> Deserialize<'de>>(
        &self,
        path: &str,
        form: &[(&str, &str)],
    ) -> Result<T, StripeError> {
        let url = format!("{STRIPE_API}/{path}");
        let resp = self
            .http
            .post(&url)
            .basic_auth(&self.secret_key, Some(""))
            .form(form)
            .send()
            .await?;
        let status = resp.status().as_u16();
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            return Err(StripeError::Api { status, body });
        }
        Ok(resp.json::<T>().await?)
    }

    /// Create a Stripe customer and return its id. We attach `user_id` as
    /// metadata so the webhook can map customer → user with one DB hit on
    /// the unique `users.stripe_customer_id` index.
    pub async fn create_customer(
        &self,
        email: &str,
        user_id: uuid::Uuid,
    ) -> Result<String, StripeError> {
        let user_id_str = user_id.to_string();
        let form = [
            ("email", email),
            ("metadata[user_id]", user_id_str.as_str()),
        ];
        let resp: CustomerResp = self.post_form("customers", &form).await?;
        Ok(resp.id)
    }

    /// Create a Checkout Session for a subscription on `price_id`, return
    /// the hosted URL the user should be redirected to.
    pub async fn create_checkout_session(
        &self,
        customer_id: &str,
        price_id: &str,
        user_id: uuid::Uuid,
    ) -> Result<String, StripeError> {
        let user_id_str = user_id.to_string();
        let form = [
            ("mode", "subscription"),
            ("customer", customer_id),
            ("line_items[0][price]", price_id),
            ("line_items[0][quantity]", "1"),
            ("success_url", self.cfg.checkout_success_url.as_str()),
            ("cancel_url", self.cfg.checkout_cancel_url.as_str()),
            ("automatic_tax[enabled]", "true"),
            ("subscription_data[metadata][user_id]", user_id_str.as_str()),
        ];
        let resp: SessionResp = self.post_form("checkout/sessions", &form).await?;
        resp.url.ok_or(StripeError::MissingField("url"))
    }

    /// Create a Customer Portal session — used by /profile's "Manage
    /// billing" button to drop the user into Stripe's hosted UI for
    /// cancel / payment-method-update / invoice-history.
    pub async fn create_portal_session(&self, customer_id: &str) -> Result<String, StripeError> {
        let form = [
            ("customer", customer_id),
            ("return_url", self.cfg.portal_return_url.as_str()),
        ];
        let resp: SessionResp = self.post_form("billing_portal/sessions", &form).await?;
        resp.url.ok_or(StripeError::MissingField("url"))
    }
}
