use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

use anyhow::Context;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Deserialize)]
pub struct WorkerRlEpisodeRecord {
    #[serde(default)]
    pub at_unix_secs: i64,
    #[serde(default)]
    pub domain: String,
    #[serde(default)]
    pub target: Option<String>,
    #[serde(default)]
    pub target_selector_policy: Option<String>,
    #[serde(default)]
    pub ga_policy: String,
    #[serde(default)]
    pub strategy_genome_fingerprint: Option<String>,
    #[serde(default)]
    pub replay_canonicals: Vec<String>,
    #[serde(default)]
    pub lake_attempts: usize,
    #[serde(default)]
    pub lake_passed: usize,
    #[serde(default)]
    pub verified_count: usize,
    #[serde(default)]
    pub reward: f64,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PolicyStats {
    pub pulls: usize,
    pub weighted_pulls: f64,
    pub reward_sum: f64,
    pub weighted_reward_sum: f64,
    #[serde(default)]
    pub reward_sq_sum: f64,
    pub lake_attempts: usize,
    pub lake_passed: usize,
    pub verified_chunks: usize,
    pub verified_count: usize,
    pub replay_uses: usize,
    pub latest_unix_secs: i64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RankedPolicy {
    pub key: String,
    pub stats: PolicyStats,
    pub mean_reward: f64,
    pub weighted_mean_reward: f64,
    #[serde(default)]
    pub reward_stddev: f64,
    #[serde(default)]
    pub reward_std_error: f64,
    pub ucb_score: f64,
    pub conservative_score: f64,
    pub lake_pass_rate: f64,
    pub low_sample: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EvaluationSnapshot {
    pub generated_at_unix_secs: i64,
    pub episodes: usize,
    pub domains: BTreeSet<String>,
    pub targets: BTreeSet<String>,
    pub latest_unix_secs: i64,
    pub half_life_hours: f64,
    pub min_pulls: usize,
    pub ga_policies: Vec<RankedPolicy>,
    pub target_selector_policies: Vec<RankedPolicy>,
    pub strategy_genomes: Vec<RankedPolicy>,
    pub domain_targets: Vec<RankedPolicy>,
}

pub fn read_episodes(path: &Path) -> anyhow::Result<Vec<WorkerRlEpisodeRecord>> {
    let file = File::open(path).with_context(|| format!("open {}", path.display()))?;
    let reader = BufReader::new(file);
    let mut episodes = Vec::new();
    for (index, line) in reader.lines().enumerate() {
        let line = line.with_context(|| format!("read line {}", index + 1))?;
        if line.trim().is_empty() {
            continue;
        }
        let episode = serde_json::from_str(&line)
            .with_context(|| format!("parse {} line {}", path.display(), index + 1))?;
        episodes.push(episode);
    }
    Ok(episodes)
}

pub fn evaluate_episodes(
    episodes: &[WorkerRlEpisodeRecord],
    half_life_hours: f64,
    min_pulls: usize,
    generated_at_unix_secs: i64,
) -> EvaluationSnapshot {
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

    EvaluationSnapshot {
        generated_at_unix_secs,
        episodes: episodes.len(),
        domains,
        targets,
        latest_unix_secs,
        half_life_hours,
        min_pulls,
        ga_policies: rank_stats(ga, min_pulls),
        target_selector_policies: rank_stats(target_policies, min_pulls),
        strategy_genomes: rank_stats(genomes, min_pulls),
        domain_targets: rank_stats(domain_targets, min_pulls),
    }
}

pub fn write_evaluation_snapshot(
    episode_path: &Path,
    output_path: &Path,
    half_life_hours: f64,
    min_pulls: usize,
    generated_at_unix_secs: i64,
) -> anyhow::Result<EvaluationSnapshot> {
    let episodes = read_episodes(episode_path)?;
    let snapshot = evaluate_episodes(
        &episodes,
        half_life_hours,
        min_pulls,
        generated_at_unix_secs,
    );
    if let Some(parent) = output_path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let tmp_path = output_path.with_extension("json.tmp");
    std::fs::write(&tmp_path, serde_json::to_vec_pretty(&snapshot)?)?;
    std::fs::rename(&tmp_path, output_path)?;
    Ok(snapshot)
}

fn update_stats(stats: &mut PolicyStats, episode: &WorkerRlEpisodeRecord, weight: f64) {
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

fn rank_stats(map: BTreeMap<String, PolicyStats>, min_pulls: usize) -> Vec<RankedPolicy> {
    let total_pulls: usize = map.values().map(|stats| stats.pulls).sum();
    let log_total = (total_pulls.max(2) as f64).ln();
    let mut ranked = map
        .into_iter()
        .map(|(key, stats)| {
            let mean_reward = stats.reward_sum / stats.pulls.max(1) as f64;
            let weighted_mean_reward =
                stats.weighted_reward_sum / stats.weighted_pulls.max(f64::EPSILON);
            let reward_variance = if stats.pulls > 1 {
                (stats.reward_sq_sum / stats.pulls as f64 - mean_reward * mean_reward).max(0.0)
            } else {
                0.25
            };
            let reward_stddev = reward_variance.sqrt();
            let reward_std_error = reward_stddev / (stats.pulls.max(1) as f64).sqrt();
            let exploration = (2.0 * log_total / stats.pulls.max(1) as f64).sqrt();
            let lake_pass_rate = ratio(stats.lake_passed, stats.lake_attempts);
            let low_sample = stats.pulls < min_pulls;
            RankedPolicy {
                key,
                stats,
                mean_reward,
                weighted_mean_reward,
                reward_stddev,
                reward_std_error,
                ucb_score: weighted_mean_reward + exploration,
                conservative_score: weighted_mean_reward - exploration,
                lake_pass_rate,
                low_sample,
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

fn ratio(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 {
        0.0
    } else {
        numerator as f64 / denominator as f64
    }
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
    ) -> WorkerRlEpisodeRecord {
        WorkerRlEpisodeRecord {
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

        let summary = evaluate_episodes(&episodes, 168.0, 2, 400);

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
