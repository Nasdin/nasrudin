//! Worker HTTP client supporting both TCP (`http://`, `https://`) and
//! unix-domain-socket (`unix:///path`) transports.
//!
//! Most of the worker codebase passed `api_url: &str` and called
//! `reqwest::Client` against it. This module replaces both with a
//! `WorkerHttp` enum that wraps either a `reqwest::Client + base url`
//! or a `hyper-util` legacy client + UDS path. Public API is
//! request-shaped:
//!
//! ```ignore
//! let http = WorkerHttp::from_env(&api_url)?;
//! let (status, json) = http.get_json("/api/seed?top=200", &[]).await?;
//! ```
//!
//! The worker constructs one `WorkerHttp` from `NASRUDIN_API_URL` at
//! boot and shares it; `Clone` is cheap (Arc inside).

use std::path::PathBuf;
use std::sync::Arc;

use anyhow::{Context, Result};
use bytes::Bytes;
use http_body_util::BodyExt;

use crate::worker_url::{parse_api_base, ApiBase};

#[derive(Clone)]
pub struct WorkerHttp {
    inner: Arc<Inner>,
}

enum Inner {
    Tcp {
        client: reqwest::Client,
        base: url::Url,
    },
    Unix {
        client: hyper_util::client::legacy::Client<
            hyperlocal::UnixConnector,
            http_body_util::Full<Bytes>,
        >,
        sock: PathBuf,
    },
}

impl WorkerHttp {
    /// Build from a `NASRUDIN_API_URL`-style string.
    pub fn from_env(api_url: &str) -> Result<Self> {
        let base = parse_api_base(api_url).map_err(|e| anyhow::anyhow!("{e}"))?;
        Ok(match base {
            ApiBase::Tcp(u) => {
                let client = reqwest::Client::builder()
                    .pool_idle_timeout(Some(std::time::Duration::from_secs(60)))
                    .build()
                    .context("reqwest client build")?;
                Self {
                    inner: Arc::new(Inner::Tcp { client, base: u }),
                }
            }
            ApiBase::Unix(p) => {
                let client = hyper_util::client::legacy::Client::builder(
                    hyper_util::rt::TokioExecutor::new(),
                )
                .build(hyperlocal::UnixConnector);
                Self {
                    inner: Arc::new(Inner::Unix { client, sock: p }),
                }
            }
        })
    }

    /// True iff this client routes traffic over a unix domain socket.
    pub fn is_unix(&self) -> bool {
        matches!(&*self.inner, Inner::Unix { .. })
    }

    /// Display string for logs (the base URL or the socket path).
    pub fn target(&self) -> String {
        match &*self.inner {
            Inner::Tcp { base, .. } => base.to_string(),
            Inner::Unix { sock, .. } => format!("unix://{}", sock.display()),
        }
    }

    /// `GET path` returning (status, body bytes). `path` must start with `/`.
    pub async fn get_bytes(
        &self,
        path: &str,
        headers: &[(&str, &str)],
    ) -> Result<(u16, Bytes)> {
        match &*self.inner {
            Inner::Tcp { client, base } => {
                let url = base.join(path).context("join path")?;
                let mut req = client.get(url);
                for (k, v) in headers {
                    req = req.header(*k, *v);
                }
                let resp = req.send().await.context("reqwest GET")?;
                let status = resp.status().as_u16();
                let bytes = resp.bytes().await.context("reqwest body")?;
                Ok((status, bytes))
            }
            Inner::Unix { client, sock } => {
                let uri: hyper::Uri = hyperlocal::Uri::new(sock, path).into();
                let mut req = hyper::Request::builder().method("GET").uri(uri);
                for (k, v) in headers {
                    req = req.header(*k, *v);
                }
                let req = req
                    .body(http_body_util::Full::new(Bytes::new()))
                    .context("hyper req build")?;
                let resp = client.request(req).await.context("hyper GET")?;
                let status = resp.status().as_u16();
                let body = resp.into_body().collect().await.context("hyper body")?.to_bytes();
                Ok((status, body))
            }
        }
    }

    /// `GET path` parsing JSON body into the requested type.
    pub async fn get_json<T: serde::de::DeserializeOwned>(
        &self,
        path: &str,
        headers: &[(&str, &str)],
    ) -> Result<(u16, T)> {
        let (status, body) = self.get_bytes(path, headers).await?;
        let v: T = serde_json::from_slice(&body)
            .with_context(|| format!("decode JSON from {path} (status {status})"))?;
        Ok((status, v))
    }

    /// `POST path` with a JSON body, returning (status, optional JSON body).
    pub async fn post_json<B: serde::Serialize, T: serde::de::DeserializeOwned + Default>(
        &self,
        path: &str,
        body: &B,
        headers: &[(&str, &str)],
    ) -> Result<(u16, T)> {
        let body_bytes = serde_json::to_vec(body).context("serialize body")?;
        let mut all_headers: Vec<(&str, &str)> =
            headers.iter().map(|(k, v)| (*k, *v)).collect();
        all_headers.push(("content-type", "application/json"));
        let (status, resp_bytes) = self.post_bytes(path, body_bytes.into(), &all_headers).await?;
        let parsed: T = if resp_bytes.is_empty() {
            T::default()
        } else {
            serde_json::from_slice(&resp_bytes)
                .with_context(|| format!("decode JSON from {path} (status {status})"))?
        };
        Ok((status, parsed))
    }

    /// `POST path` with a raw byte body. Returns (status, response body bytes).
    pub async fn post_bytes(
        &self,
        path: &str,
        body: Bytes,
        headers: &[(&str, &str)],
    ) -> Result<(u16, Bytes)> {
        match &*self.inner {
            Inner::Tcp { client, base } => {
                let url = base.join(path).context("join path")?;
                let mut req = client.post(url).body(body.to_vec());
                for (k, v) in headers {
                    req = req.header(*k, *v);
                }
                let resp = req.send().await.context("reqwest POST")?;
                let status = resp.status().as_u16();
                let bytes = resp.bytes().await.context("reqwest body")?;
                Ok((status, bytes))
            }
            Inner::Unix { client, sock } => {
                let uri: hyper::Uri = hyperlocal::Uri::new(sock, path).into();
                let mut req = hyper::Request::builder().method("POST").uri(uri);
                for (k, v) in headers {
                    req = req.header(*k, *v);
                }
                let req = req
                    .body(http_body_util::Full::new(body))
                    .context("hyper req build")?;
                let resp = client.request(req).await.context("hyper POST")?;
                let status = resp.status().as_u16();
                let body = resp.into_body().collect().await.context("hyper body")?.to_bytes();
                Ok((status, body))
            }
        }
    }

    /// `DELETE path`. Returns the status code.
    pub async fn delete(&self, path: &str, headers: &[(&str, &str)]) -> Result<u16> {
        match &*self.inner {
            Inner::Tcp { client, base } => {
                let url = base.join(path).context("join path")?;
                let mut req = client.delete(url);
                for (k, v) in headers {
                    req = req.header(*k, *v);
                }
                let resp = req.send().await.context("reqwest DELETE")?;
                Ok(resp.status().as_u16())
            }
            Inner::Unix { client, sock } => {
                let uri: hyper::Uri = hyperlocal::Uri::new(sock, path).into();
                let mut req = hyper::Request::builder().method("DELETE").uri(uri);
                for (k, v) in headers {
                    req = req.header(*k, *v);
                }
                let req = req
                    .body(http_body_util::Full::new(Bytes::new()))
                    .context("hyper req build")?;
                let resp = client.request(req).await.context("hyper DELETE")?;
                Ok(resp.status().as_u16())
            }
        }
    }
}
