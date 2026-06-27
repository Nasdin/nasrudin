use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    fs::File,
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
};

use anyhow::{Context, bail};
use serde::Deserialize;

#[derive(Debug, Clone, Deserialize)]
struct WorkerRlEpisode {
    #[serde(default)]
    at_unix_secs: i64,
    #[serde(default)]
    domain: String,
    #[serde(default)]
    target: Option<String>,
    #[serde(default)]
    target_selector_policy: Option<String>,
    #[serde(default)]
    ga_policy: String,
    #[serde(default)]
    strategy_genome_fingerprint: Option<String>,
    #[serde(default)]
    replay_canonicals: Vec<String>,
    #[serde(default)]
    lake_attempts: usize,
    #[serde(default)]
    lake_passed: usize,
    #[serde(default)]
    verified_count: usize,
    #[serde(default)]
    reward: f64,
}

#[derive(Debug, Clone, Default)]
struct PolicyStats {
    pulls: usize,
    weighted_pulls: f64,
    reward_sum: f64,
    weighted_reward_sum: f64,
    reward_sq_sum: f64,
    lake_attempts: usize,
    lake_passed: usize,
    verified_chunks: usize,
    verified_count: usize,
    replay_uses: usize,
    latest_unix_secs: i64,
}

#[derive(Debug, Clone)]
struct RankedPolicy {
    key: String,
    stats: PolicyStats,
    mean_reward: f64,
    weighted_mean_reward: f64,
    ucb_score: f64,
    conservative_score: f64,
}

fn main() -> anyhow::Result<()> {
    let opts = Options::parse(env::args().skip(1).collect())?;
    let episodes = read_episodes(&opts.path)?;
    if episodes.is_empty() {
        bail!("no RL episodes found in {}", opts.path.display());
    }

    let summary = evaluate(&episodes, opts.half_life_hours);
    if opts.json {
        print_json(&summary)?;
    } else {
        print_human(&opts.path, &summary, opts.min_pulls);
    }
    Ok(())
}

#[derive(Debug, Clone)]
struct Options {
    path: PathBuf,
    half_life_hours: f64,
    min_pulls: usize,
    json: bool,
}

impl Options {
    fn parse(args: Vec<String>) -> anyhow::Result<Self> {
        let mut path = None;
        let mut half_life_hours = 168.0;
        let mut min_pulls = 3;
        let mut json = false;
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "-h" | "--help" => {
                    print_usage();
                    std::process::exit(0);
                }
                "--json" => {
                    json = true;
                    i += 1;
                }
                "--half-life-hours" => {
                    let value = args
                        .get(i + 1)
                        .context("--half-life-hours requires a value")?;
                    half_life_hours = value
                        .parse()
                        .context("--half-life-hours must be a number")?;
                    if half_life_hours < 0.0 {
                        bail!("--half-life-hours must be >= 0");
                    }
                    i += 2;
                }
                "--min-pulls" => {
                    let value = args.get(i + 1).context("--min-pulls requires a value")?;
                    min_pulls = value.parse().context("--min-pulls must be an integer")?;
                    i += 2;
                }
                value if value.starts_with('-') => {
                    bail!("unknown flag: {value}");
                }
                value => {
                    if path.is_some() {
                        bail!("expected one episode log path, got another positional: {value}");
                    }
                    path = Some(PathBuf::from(value));
                    i += 1;
                }
            }
        }

        let path = path
            .or_else(|| {
                env::var("NASRUDIN_RL_EPISODE_LOG_PATH")
                    .ok()
                    .map(PathBuf::from)
            })
            .context(
                "episode log path required; pass a path or set NASRUDIN_RL_EPISODE_LOG_PATH",
            )?;

        Ok(Self {
            path,
            half_life_hours,
            min_pulls,
            json,
        })
    }
}

#[derive(Debug)]
struct EvaluationSummary {
    episodes: usize,
    domains: BTreeSet<String>,
    targets: BTreeSet<String>,
    latest_unix_secs: i64,
    half_life_hours: f64,
    ga_policies: Vec<RankedPolicy>,
    target_selector_policies: Vec<RankedPolicy>,
    strategy_genomes: Vec<RankedPolicy>,
    domain_targets: Vec<RankedPolicy>,
}

fn evaluate(episodes: &[WorkerRlEpisode], half_life_hours: f64) -> EvaluationSummary {
    let latest_unix_secs = episodes
        .iter()
        .map(|episode| episode.at_unix_secs)
        .max()
        .unwrap_or_default();
    let mut domains = BTreeSet::new();
    let mut targets = BTreeSet::new();
    let mut ga = BTreeMap::new();
    let mut target_policies = BTreeMap::new();
    let mut genomes = BTreeMap::new();
    let mut domain_targets = BTreeMap::new();

    for episode in episodes {
        if !episode.domain.is_empty() {
            domains.insert(episode.domain.clone());
        }
        if let Some(target) = &episode.target {
            targets.insert(target.clone());
        }
        let weight = recency_weight(
            latest_unix_secs.saturating_sub(episode.at_unix_secs),
            half_life_hours,
        );
        update_stats(
            ga.entry(nonempty_or(&episode.ga_policy, "unknown"))
                .or_default(),
            episode,
            weight,
        );
        if let Some(policy) = &episode.target_selector_policy {
            update_stats(
                target_policies
                    .entry(nonempty_or(policy, "unknown"))
                    .or_default(),
                episode,
                weight,
            );
        }
        if let Some(fingerprint) = &episode.strategy_genome_fingerprint {
            update_stats(
                genomes
                    .entry(nonempty_or(fingerprint, "unknown"))
                    .or_default(),
                episode,
                weight,
            );
        }
        let target = episode.target.as_deref().unwrap_or("untargeted");
        update_stats(
            domain_targets
                .entry(format!(
                    "{}:{}",
                    nonempty_or(&episode.domain, "unknown"),
                    target
                ))
                .or_default(),
            episode,
            weight,
        );
    }

    EvaluationSummary {
        episodes: episodes.len(),
        domains,
        targets,
        latest_unix_secs,
        half_life_hours,
        ga_policies: rank_stats(ga),
        target_selector_policies: rank_stats(target_policies),
        strategy_genomes: rank_stats(genomes),
        domain_targets: rank_stats(domain_targets),
    }
}

fn read_episodes(path: &Path) -> anyhow::Result<Vec<WorkerRlEpisode>> {
    let file = File::open(path).with_context(|| format!("open {}", path.display()))?;
    let reader = BufReader::new(file);
    let mut episodes = Vec::new();
    for (index, line) in reader.lines().enumerate() {
        let line = line.with_context(|| format!("read line {}", index + 1))?;
        if line.trim().is_empty() {
            continue;
        }
        let episode: WorkerRlEpisode =
            serde_json::from_str(&line).with_context(|| format!("parse line {}", index + 1))?;
        episodes.push(episode);
    }
    Ok(episodes)
}

fn update_stats(stats: &mut PolicyStats, episode: &WorkerRlEpisode, weight: f64) {
    stats.pulls += 1;
    stats.weighted_pulls += weight;
    stats.reward_sum += episode.reward;
    stats.weighted_reward_sum += episode.reward * weight;
    stats.reward_sq_sum += episode.reward * episode.reward;
    stats.lake_attempts += episode.lake_attempts;
    stats.lake_passed += episode.lake_passed;
    stats.verified_count += episode.verified_count;
    stats.replay_uses += episode.replay_canonicals.len();
    stats.latest_unix_secs = stats.latest_unix_secs.max(episode.at_unix_secs);
    if episode.verified_count > 0 {
        stats.verified_chunks += 1;
    }
}

fn rank_stats(map: BTreeMap<String, PolicyStats>) -> Vec<RankedPolicy> {
    let total_pulls: usize = map.values().map(|stats| stats.pulls).sum();
    let log_total = (total_pulls.max(2) as f64).ln();
    let mut ranked = map
        .into_iter()
        .map(|(key, stats)| {
            let mean_reward = stats.reward_sum / stats.pulls.max(1) as f64;
            let weighted_mean_reward =
                stats.weighted_reward_sum / stats.weighted_pulls.max(f64::EPSILON);
            let exploration = (2.0 * log_total / stats.pulls.max(1) as f64).sqrt();
            RankedPolicy {
                key,
                stats,
                mean_reward,
                weighted_mean_reward,
                ucb_score: weighted_mean_reward + exploration,
                conservative_score: weighted_mean_reward - exploration,
            }
        })
        .collect::<Vec<_>>();
    ranked.sort_by(|a, b| {
        b.conservative_score
            .total_cmp(&a.conservative_score)
            .then_with(|| b.weighted_mean_reward.total_cmp(&a.weighted_mean_reward))
            .then_with(|| b.stats.pulls.cmp(&a.stats.pulls))
            .then_with(|| a.key.cmp(&b.key))
    });
    ranked
}

fn recency_weight(age_seconds: i64, half_life_hours: f64) -> f64 {
    if half_life_hours <= 0.0 {
        return 1.0;
    }
    let half_life_seconds = half_life_hours * 3600.0;
    0.5_f64.powf(age_seconds.max(0) as f64 / half_life_seconds)
}

fn nonempty_or(value: &str, fallback: &str) -> String {
    let value = value.trim();
    if value.is_empty() {
        fallback.to_string()
    } else {
        value.to_string()
    }
}

fn print_human(path: &Path, summary: &EvaluationSummary, min_pulls: usize) {
    println!("Nasrudin RL episode evaluation");
    println!("  log: {}", path.display());
    println!("  episodes: {}", summary.episodes);
    println!("  latest_unix_secs: {}", summary.latest_unix_secs);
    println!("  half_life_hours: {:.2}", summary.half_life_hours);
    println!("  domains: {}", comma_set(&summary.domains));
    println!("  targets: {}", comma_set(&summary.targets));
    print_ranked("GA workhorse policies", &summary.ga_policies, min_pulls);
    print_ranked(
        "Target selector policies",
        &summary.target_selector_policies,
        min_pulls,
    );
    print_ranked("Strategy genomes", &summary.strategy_genomes, min_pulls);
    print_ranked(
        "Domain/target curriculum",
        &summary.domain_targets,
        min_pulls,
    );
}

fn print_ranked(title: &str, ranked: &[RankedPolicy], min_pulls: usize) {
    println!();
    println!("{title}:");
    if ranked.is_empty() {
        println!("  (no data)");
        return;
    }
    println!(
        "  {:<34} {:>5} {:>8} {:>8} {:>8} {:>8} {:>8}",
        "key", "pulls", "w_mean", "mean", "ucb", "lcb", "lake"
    );
    for row in ranked.iter().take(12) {
        let lake_rate = ratio(row.stats.lake_passed, row.stats.lake_attempts);
        let sample_note = if row.stats.pulls < min_pulls {
            " low-n"
        } else {
            ""
        };
        println!(
            "  {:<34} {:>5} {:>8.3} {:>8.3} {:>8.3} {:>8.3} {:>7.1}%{}",
            truncate(&row.key, 34),
            row.stats.pulls,
            row.weighted_mean_reward,
            row.mean_reward,
            row.ucb_score,
            row.conservative_score,
            lake_rate * 100.0,
            sample_note
        );
    }
}

fn print_json(summary: &EvaluationSummary) -> anyhow::Result<()> {
    let json = serde_json::json!({
        "episodes": summary.episodes,
        "latest_unix_secs": summary.latest_unix_secs,
        "half_life_hours": summary.half_life_hours,
        "domains": summary.domains,
        "targets": summary.targets,
        "ga_policies": ranked_json(&summary.ga_policies),
        "target_selector_policies": ranked_json(&summary.target_selector_policies),
        "strategy_genomes": ranked_json(&summary.strategy_genomes),
        "domain_targets": ranked_json(&summary.domain_targets),
    });
    println!("{}", serde_json::to_string_pretty(&json)?);
    Ok(())
}

fn ranked_json(ranked: &[RankedPolicy]) -> Vec<serde_json::Value> {
    ranked
        .iter()
        .map(|row| {
            serde_json::json!({
                "key": row.key,
                "pulls": row.stats.pulls,
                "weighted_pulls": row.stats.weighted_pulls,
                "mean_reward": row.mean_reward,
                "weighted_mean_reward": row.weighted_mean_reward,
                "ucb_score": row.ucb_score,
                "conservative_score": row.conservative_score,
                "lake_attempts": row.stats.lake_attempts,
                "lake_passed": row.stats.lake_passed,
                "lake_pass_rate": ratio(row.stats.lake_passed, row.stats.lake_attempts),
                "verified_chunks": row.stats.verified_chunks,
                "verified_count": row.stats.verified_count,
                "replay_uses": row.stats.replay_uses,
                "latest_unix_secs": row.stats.latest_unix_secs,
            })
        })
        .collect()
}

fn ratio(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 {
        0.0
    } else {
        numerator as f64 / denominator as f64
    }
}

fn comma_set(values: &BTreeSet<String>) -> String {
    if values.is_empty() {
        "(none)".to_string()
    } else {
        values.iter().cloned().collect::<Vec<_>>().join(", ")
    }
}

fn truncate(value: &str, max_chars: usize) -> String {
    if value.chars().count() <= max_chars {
        return value.to_string();
    }
    let mut out = value
        .chars()
        .take(max_chars.saturating_sub(1))
        .collect::<String>();
    out.push('…');
    out
}

fn print_usage() {
    println!(
        "Usage: rl_episode_eval [OPTIONS] <worker_rl_episodes.jsonl>\n\
         \n\
         Options:\n\
           --json                         Emit machine-readable JSON\n\
           --half-life-hours <hours>      Recency half-life for weighted rewards [default: 168]\n\
           --min-pulls <n>                Mark rows below this sample count as low-n [default: 3]\n\
           -h, --help                     Show this help"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn episode(
        at_unix_secs: i64,
        ga_policy: &str,
        target_policy: &str,
        target: &str,
        reward: f64,
        lake_passed: usize,
    ) -> WorkerRlEpisode {
        WorkerRlEpisode {
            at_unix_secs,
            domain: "qm".to_string(),
            target: Some(target.to_string()),
            target_selector_policy: Some(target_policy.to_string()),
            ga_policy: ga_policy.to_string(),
            strategy_genome_fingerprint: None,
            replay_canonicals: Vec::new(),
            lake_attempts: 1,
            lake_passed,
            verified_count: lake_passed,
            reward,
        }
    }

    #[test]
    fn evaluation_ranks_policy_by_conservative_recency_weighted_reward() {
        let episodes = vec![
            episode(100, "wide_explore", "novelty_seeker", "qm_a", 0.1, 0),
            episode(200, "steady_verify", "verifier_ucb", "qm_a", 1.0, 1),
            episode(300, "steady_verify", "verifier_ucb", "qm_a", 1.0, 1),
        ];

        let summary = evaluate(&episodes, 168.0);

        assert_eq!(summary.ga_policies[0].key, "steady_verify");
        assert_eq!(summary.ga_policies[0].stats.pulls, 2);
        assert_eq!(summary.ga_policies[0].stats.lake_passed, 2);
        assert_eq!(summary.target_selector_policies[0].key, "verifier_ucb");
    }

    #[test]
    fn zero_half_life_disables_recency_decay() {
        assert_eq!(recency_weight(10_000, 0.0), 1.0);
    }
}
