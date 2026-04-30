//! Stripe API client built on async-stripe.
//!
//! Wraps `stripe::Client` with a `BillingConfig` carrying our env-var
//! values (price ids, redirect URLs, webhook secret) so handlers don't
//! have to thread them through individually.

use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;

use stripe::{
    BillingPortalSession, CheckoutSession, CheckoutSessionMode, Client, CreateBillingPortalSession,
    CreateCheckoutSession, CreateCheckoutSessionAutomaticTax, CreateCheckoutSessionLineItems,
    CreateCheckoutSessionSubscriptionData, CreateCustomer, Customer, CustomerId, Expandable,
    Subscription,
};

#[derive(Clone)]
pub struct BillingConfig {
    pub price_researcher_monthly: String,
    pub price_researcher_annual: String,
    /// Recurring monthly sponsor tiers — donations, not service tiers.
    /// Webhook maps these to `PlanTier::Free`.
    pub price_sponsor_5: String,
    pub price_sponsor_25: String,
    pub price_sponsor_100: String,
    /// Stripe Payment Link URL for one-time, name-your-amount donations.
    /// Frontend links straight to it; no checkout endpoint involved.
    pub sponsor_payment_link: String,
    pub checkout_success_url: String,
    pub checkout_cancel_url: String,
    pub portal_return_url: String,
    pub webhook_secret: String,
}

#[derive(Clone)]
pub struct BillingClient {
    pub stripe: Client,
    pub cfg: Arc<BillingConfig>,
}

#[derive(Debug, thiserror::Error)]
pub enum StripeError {
    #[error("stripe: {0}")]
    Stripe(#[from] stripe::StripeError),
    #[error("missing field in stripe response: {0}")]
    MissingField(&'static str),
    #[error("malformed customer id: {0}")]
    BadCustomerId(String),
}

impl BillingClient {
    pub fn from_env() -> anyhow::Result<Self> {
        let secret_key = std::env::var("STRIPE_SECRET_KEY")
            .map_err(|_| anyhow::anyhow!("STRIPE_SECRET_KEY not set"))?;
        let cfg = BillingConfig {
            price_researcher_monthly: std::env::var("STRIPE_PRICE_RESEARCHER_MONTHLY")?,
            price_researcher_annual: std::env::var("STRIPE_PRICE_RESEARCHER_ANNUAL")?,
            price_sponsor_5: std::env::var("STRIPE_PRICE_SPONSOR_5").unwrap_or_default(),
            price_sponsor_25: std::env::var("STRIPE_PRICE_SPONSOR_25").unwrap_or_default(),
            price_sponsor_100: std::env::var("STRIPE_PRICE_SPONSOR_100").unwrap_or_default(),
            sponsor_payment_link: std::env::var("STRIPE_SPONSOR_PAYMENT_LINK")
                .unwrap_or_default(),
            checkout_success_url: std::env::var("STRIPE_CHECKOUT_SUCCESS_URL")?,
            checkout_cancel_url: std::env::var("STRIPE_CHECKOUT_CANCEL_URL")?,
            portal_return_url: std::env::var("STRIPE_CUSTOMER_PORTAL_RETURN_URL")?,
            webhook_secret: std::env::var("STRIPE_WEBHOOK_SECRET")?,
        };
        Ok(Self {
            stripe: Client::new(secret_key),
            cfg: Arc::new(cfg),
        })
    }

    /// Create a Stripe customer and return its id. We attach `user_id` as
    /// metadata so the webhook can map customer → user with one DB hit on
    /// the unique `users.stripe_customer_id` index.
    pub async fn create_customer(
        &self,
        email: &str,
        user_id: uuid::Uuid,
    ) -> Result<String, StripeError> {
        let mut params = CreateCustomer::new();
        params.email = Some(email);
        let mut metadata = HashMap::new();
        metadata.insert("user_id".to_string(), user_id.to_string());
        params.metadata = Some(metadata);
        let customer = Customer::create(&self.stripe, params).await?;
        Ok(customer.id.to_string())
    }

    /// Create a Checkout Session for a subscription on `price_id`, return
    /// the hosted URL the user should be redirected to. Stripe Tax is
    /// enabled so EU/UK VAT is collected without extra app code.
    pub async fn create_checkout_session(
        &self,
        customer_id: &str,
        price_id: &str,
        user_id: uuid::Uuid,
    ) -> Result<String, StripeError> {
        let cust = CustomerId::from_str(customer_id)
            .map_err(|_| StripeError::BadCustomerId(customer_id.to_string()))?;
        let mut params = CreateCheckoutSession::new();
        params.mode = Some(CheckoutSessionMode::Subscription);
        params.customer = Some(cust);
        params.success_url = Some(self.cfg.checkout_success_url.as_str());
        params.cancel_url = Some(self.cfg.checkout_cancel_url.as_str());
        params.line_items = Some(vec![CreateCheckoutSessionLineItems {
            price: Some(price_id.to_string()),
            quantity: Some(1),
            ..Default::default()
        }]);
        let mut sub_metadata = HashMap::new();
        sub_metadata.insert("user_id".to_string(), user_id.to_string());
        params.subscription_data = Some(CreateCheckoutSessionSubscriptionData {
            metadata: Some(sub_metadata),
            ..Default::default()
        });
        params.automatic_tax = Some(CreateCheckoutSessionAutomaticTax {
            enabled: true,
            ..Default::default()
        });
        let session = CheckoutSession::create(&self.stripe, params).await?;
        session
            .url
            .ok_or(StripeError::MissingField("checkout_session.url"))
    }

    /// Open a Customer Portal session — used by the /profile "Manage
    /// billing" button so users can self-serve cancel, change payment
    /// method, or view invoices.
    pub async fn create_portal_session(&self, customer_id: &str) -> Result<String, StripeError> {
        let cust = CustomerId::from_str(customer_id)
            .map_err(|_| StripeError::BadCustomerId(customer_id.to_string()))?;
        let mut params = CreateBillingPortalSession::new(cust);
        params.return_url = Some(self.cfg.portal_return_url.as_str());
        let session = BillingPortalSession::create(&self.stripe, params).await?;
        Ok(session.url)
    }
}

/// Pull a `customer` id out of either a fully-resolved `Customer` object
/// or an unexpanded id reference. Stripe's webhook payloads send
/// unexpanded ids by default.
pub fn customer_id_from_expandable(c: &Expandable<Customer>) -> Option<String> {
    match c {
        Expandable::Id(id) => Some(id.to_string()),
        Expandable::Object(obj) => Some(obj.id.to_string()),
    }
}

/// Pull the price id out of the first subscription item (Phase 1: every
/// subscription has exactly one item — the Researcher seat).
pub fn first_price_id(sub: &Subscription) -> Option<String> {
    sub.items
        .data
        .first()
        .and_then(|item| item.price.as_ref())
        .map(|p| p.id.to_string())
}
