//! API base parsing for the worker binary.
//!
//! Recognizes:
//! - `http://...`     → `ApiBase::Tcp`
//! - `https://...`    → `ApiBase::Tcp`
//! - `unix:///path`   → `ApiBase::Unix`
//!
//! The worker picks the corresponding HTTP client based on this
//! discriminant. Unix-socket connections still send a normal HTTP/1.1
//! request — the UDS only changes transport, not the wire protocol.

use std::path::PathBuf;

#[derive(Clone, Debug)]
pub enum ApiBase {
    Tcp(url::Url),
    Unix(PathBuf),
}

#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("malformed url: {0}")]
    Url(String),
    #[error("unix scheme requires absolute path: {0}")]
    UnixNoPath(String),
    #[error("unsupported scheme '{0}' (use http://, https://, or unix:///)")]
    UnsupportedScheme(String),
}

pub fn parse_api_base(input: &str) -> Result<ApiBase, ParseError> {
    if let Some(rest) = input.strip_prefix("unix://") {
        if rest.is_empty() {
            return Err(ParseError::UnixNoPath(input.into()));
        }
        return Ok(ApiBase::Unix(PathBuf::from(rest)));
    }
    let parsed = url::Url::parse(input).map_err(|e| ParseError::Url(e.to_string()))?;
    match parsed.scheme() {
        "http" | "https" => Ok(ApiBase::Tcp(parsed)),
        s => Err(ParseError::UnsupportedScheme(s.into())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_tcp_url() {
        let b = parse_api_base("http://localhost:3001").unwrap();
        assert!(matches!(b, ApiBase::Tcp(ref u) if u.as_str() == "http://localhost:3001/"));
    }

    #[test]
    fn parses_https() {
        assert!(matches!(
            parse_api_base("https://api.nasrudin.org").unwrap(),
            ApiBase::Tcp(_)
        ));
    }

    #[test]
    fn parses_unix_url() {
        let b = parse_api_base("unix:///run/nasrudin/api-local.sock").unwrap();
        assert!(matches!(b, ApiBase::Unix(ref p) if p.as_os_str() == "/run/nasrudin/api-local.sock"));
    }

    #[test]
    fn rejects_unknown_scheme() {
        assert!(matches!(
            parse_api_base("ftp://x").unwrap_err(),
            ParseError::UnsupportedScheme(_)
        ));
    }

    #[test]
    fn rejects_unix_without_path() {
        assert!(matches!(
            parse_api_base("unix://").unwrap_err(),
            ParseError::UnixNoPath(_)
        ));
    }
}
