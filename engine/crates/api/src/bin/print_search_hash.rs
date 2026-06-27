//! Debug helper: print canonical + AC-canonical hash for an input string.
//!
//! Usage: `cargo run -p physics-api --bin print_search_hash -- <format> <input>`
//! where `<format>` is one of `sexpr | math | latex`.

use nasrudin_core::{canonical_ac_hash, canonical_ac_string, parse};

fn main() -> anyhow::Result<()> {
    let mut args = std::env::args().skip(1);
    let format = args
        .next()
        .ok_or_else(|| anyhow::anyhow!("missing format"))?;
    let input = args.collect::<Vec<_>>().join(" ");
    let expr = match format.as_str() {
        "sexpr" => parse::parse_sexpr(&input).map_err(|e| anyhow::anyhow!("{e}"))?,
        "math" => parse::parse_simple(&input).map_err(|e| anyhow::anyhow!("{e}"))?,
        "latex" => parse::parse_latex(&input).map_err(|e| anyhow::anyhow!("{e}"))?,
        other => anyhow::bail!("unknown format {other}"),
    };
    println!("canonical:    {}", expr.to_canonical());
    println!("canonical_ac: {}", canonical_ac_string(&expr));
    println!("ac_hash_hex:  {}", hex::encode(canonical_ac_hash(&expr)));
    Ok(())
}
