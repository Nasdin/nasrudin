//! Stripe API client built on async-stripe 1.0.
//!
//! Wraps `stripe::Client` with a `BillingConfig` carrying our env-var
//! values (price ids, redirect URLs, webhook secret) so handlers don't
//! have to thread them through individually.
//!
//! async-stripe 1.0 split the SDK into per-product crates. The shape:
//!   - `stripe`        (async-stripe)        — `Client`, top-level error
//!   - `stripe_core`   (async-stripe-core)   — `Customer`
//!   - `stripe_checkout`                     — `CheckoutSession` + create
//!   - `stripe_billing`                      — `BillingPortalSession`
//!   - `stripe_shared`                       — `Subscription`, ID types
//!   - `stripe_types`                        — `Expandable`
//!
//! Every Create*/Update*/etc. is a builder; the request is dispatched
//! via `.send(&client).await?` rather than the old free-function form.

use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;

use stripe::Client;
use stripe_billing::billing_portal_session::CreateBillingPortalSession;
use stripe_checkout::checkout_session::{
    CreateCheckoutSession, CreateCheckoutSessionAutomaticTax,
    CreateCheckoutSessionCustomerUpdate, CreateCheckoutSessionCustomerUpdateAddress,
    CreateCheckoutSessionLineItems, CreateCheckoutSessionSubscriptionData,
};
use stripe_core::customer::CreateCustomer;
use stripe_shared::{
    CheckoutSessionMode, CheckoutSessionSubmitType, Customer, CustomerId, Subscription,
};
use stripe_types::Expandable;

#[derive(Clone)]
pub struct BillingConfig {
    pub price_researcher_monthly: String,
    pub price_researcher_annual: String,
    /// Recurring monthly sponsor tiers — donations, not service tiers.
    /// Webhook maps these to `PlanTier::Free`.
    pub price_sponsor_5: String,
    pub price_sponsor_25: String,
    pub price_sponsor_100: String,
    /// Pay-what-you-want one-time sponsor price (customer-adjustable
    /// amount). Wired into a `mode=payment` Checkout Session with
    /// `submit_type=donate`; webhook maps the resulting charge to a
    /// `kind='one_time'` row in `user_sponsorships`.
    pub price_sponsor_open: String,
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
            price_sponsor_open: std::env::var("STRIPE_PRICE_SPONSOR_OPEN").unwrap_or_default(),
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
        let mut metadata = HashMap::new();
        metadata.insert("user_id".to_string(), user_id.to_string());
        let customer = CreateCustomer::new()
            .email(email)
            .metadata(metadata)
            .send(&self.stripe)
            .await?;
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
        // Validate the customer id parses, even though we pass the raw
        // string into the builder — keeps the error surface unchanged.
        let _cust = CustomerId::from_str(customer_id)
            .map_err(|_| StripeError::BadCustomerId(customer_id.to_string()))?;
        let line_items = vec![CreateCheckoutSessionLineItems {
            price: Some(price_id.to_string()),
            quantity: Some(1),
            ..Default::default()
        }];
        let mut sub_metadata = HashMap::new();
        sub_metadata.insert("user_id".to_string(), user_id.to_string());
        let subscription_data = CreateCheckoutSessionSubscriptionData {
            metadata: Some(sub_metadata),
            ..Default::default()
        };
        let automatic_tax = CreateCheckoutSessionAutomaticTax::new(true);
        // Stripe Tax needs a resolvable customer address; ours are
        // created from email only. Tell Checkout to write the billing
        // address the user enters back to `customer.address` so the tax
        // engine can compute it. Without this Stripe rejects the session
        // with `customer-tax-location-invalid`.
        let customer_update = CreateCheckoutSessionCustomerUpdate {
            address: Some(CreateCheckoutSessionCustomerUpdateAddress::Auto),
            ..Default::default()
        };
        let session = CreateCheckoutSession::new()
            .mode(CheckoutSessionMode::Subscription)
            .customer(customer_id)
            .customer_update(customer_update)
            .success_url(self.cfg.checkout_success_url.as_str())
            .cancel_url(self.cfg.checkout_cancel_url.as_str())
            .line_items(line_items)
            .subscription_data(subscription_data)
            .automatic_tax(automatic_tax)
            .send(&self.stripe)
            .await?;
        session
            .url
            .ok_or(StripeError::MissingField("checkout_session.url"))
    }

    /// Create a Checkout Session for a one-time, customer-adjustable
    /// donation. Returns the hosted URL. Stripe renders an amount
    /// input on the page because the price has `unit_amount=null`;
    /// `submit_type=donate` reframes the CTA from "Pay" to "Donate".
    ///
    /// We intentionally do NOT enable `automatic_tax` here — donations
    /// are gifts, not taxable supplies. The recipient is the
    /// not-for-profit operator; the donor's local jurisdiction
    /// determines deductibility, which we don't claim.
    pub async fn create_donation_session(
        &self,
        customer_id: &str,
        price_id: &str,
        user_id: uuid::Uuid,
    ) -> Result<String, StripeError> {
        let _cust = CustomerId::from_str(customer_id)
            .map_err(|_| StripeError::BadCustomerId(customer_id.to_string()))?;
        let line_items = vec![CreateCheckoutSessionLineItems {
            price: Some(price_id.to_string()),
            quantity: Some(1),
            ..Default::default()
        }];
        let mut metadata = HashMap::new();
        metadata.insert("user_id".to_string(), user_id.to_string());
        metadata.insert("kind".to_string(), "sponsor_open".to_string());
        let session = CreateCheckoutSession::new()
            .mode(CheckoutSessionMode::Payment)
            .submit_type(CheckoutSessionSubmitType::Donate)
            .customer(customer_id)
            .success_url(self.cfg.checkout_success_url.as_str())
            .cancel_url(self.cfg.checkout_cancel_url.as_str())
            .line_items(line_items)
            .metadata(metadata)
            .send(&self.stripe)
            .await?;
        session
            .url
            .ok_or(StripeError::MissingField("checkout_session.url"))
    }

    /// Open a Customer Portal session — used by the /profile "Manage
    /// billing" button so users can self-serve cancel, change payment
    /// method, or view invoices.
    pub async fn create_portal_session(&self, customer_id: &str) -> Result<String, StripeError> {
        let _cust = CustomerId::from_str(customer_id)
            .map_err(|_| StripeError::BadCustomerId(customer_id.to_string()))?;
        let session = CreateBillingPortalSession::new()
            .customer(customer_id)
            .return_url(self.cfg.portal_return_url.as_str())
            .send(&self.stripe)
            .await?;
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
///
/// async-stripe 1.0: `SubscriptionItem.price` is now a non-optional
/// `Price` (was `Option<Price>` in 0.x), so the inner `.as_ref()` is
/// gone.
pub fn first_price_id(sub: &Subscription) -> Option<String> {
    sub.items.data.first().map(|item| item.price.id.to_string())
}
