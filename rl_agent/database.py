import os
import json
import psycopg2
import numpy as np
from dotenv import load_dotenv

# Load environment variables from .env
load_dotenv()

DB_USER = os.getenv("POSTGRES_USER", "physics")
DB_PASSWORD = os.getenv("POSTGRES_PASSWORD", "physics_dev")
DB_NAME = os.getenv("POSTGRES_DB", "physics_generator")
DB_PORT = os.getenv("POSTGRES_PORT", "5432")
DB_HOST = "localhost"

def get_db_connection():
    return psycopg2.connect(
        user=DB_USER,
        password=DB_PASSWORD,
        database=DB_NAME,
        host=DB_HOST,
        port=DB_PORT
    )

def fetch_historical_transitions():
    """
    Query the database to reconstruct historical transitions (state, action, reward, next_state, done)
    for offline RL pre-training and automated online fine-tuning.
    """
    conn = get_db_connection()
    cur = conn.cursor()
    
    # Fetch all completed cluster steering cycles
    cur.execute("""
        SELECT id, scope, config_json, outcome_json, started_at, ended_at 
        FROM cluster_steering 
        WHERE ended_at IS NOT NULL 
        ORDER BY started_at ASC
    """)
    cycles = cur.fetchall()
    
    transitions = []
    domains = [
        "special_relativity",
        "electromagnetism",
        "quantum_mechanics",
        "thermodynamics",
        "classical_mechanics",
        "general_relativity"
    ]
    
    for idx, cycle in enumerate(cycles[:-1]):
        cycle_id, scope, config_json, outcome_json, started_at, ended_at = cycle
        next_cycle = cycles[idx + 1]
        next_cycle_id, _, _, next_outcome_json, next_started_at, _ = next_cycle
        
        # 1. Reconstruct state at cycle T from outcome_json
        state = np.zeros((6, 8), dtype=np.float32)
        if outcome_json:
            # Parse outcome_json to extract island metrics
            # If outcome_json is a string, parse it
            if isinstance(outcome_json, str):
                outcome = json.loads(outcome_json)
            else:
                outcome = outcome_json
                
            # Extract metrics for each domain
            for d_idx, domain in enumerate(domains):
                domain_metrics = outcome.get(domain, {})
                state[d_idx, 0] = domain_metrics.get("k_used", 6) / 12.0
                state[d_idx, 1] = domain_metrics.get("mean_fitness", 0.1)
                state[d_idx, 2] = domain_metrics.get("max_fitness", 0.1)
                state[d_idx, 3] = (domain_metrics.get("silhouette", 0.0) + 1.0) / 2.0
                state[d_idx, 4] = domain_metrics.get("novelty_trend", 0.2)
                state[d_idx, 5] = domain_metrics.get("stagnation_chunks", 0.0) / 10.0
                state[d_idx, 6] = domain_metrics.get("verified_count", 0.0)
                state[d_idx, 7] = domain_metrics.get("lake_passed", 0.0)
        else:
            # Default state
            for d_idx in range(6):
                state[d_idx] = [0.5, 0.1, 0.1, 0.5, 0.2, 0.0, 0.0, 0.0]
                
        # 2. Reconstruct action taken at cycle T from config_json
        action = np.zeros((6, 5), dtype=np.float32)
        if config_json:
            if isinstance(config_json, str):
                config = json.loads(config_json)
            else:
                config = config_json
                
            # Extract target_k and domain policies
            domain_weights = config.get("domain_weights", {})
            extension = config.get("extension", {})
            strategy_genome = extension.get("strategy_genome_v1", {}) if isinstance(extension, dict) else {}
            domain_policies = strategy_genome.get("domain_policies", {}) if isinstance(strategy_genome, dict) else {}
            
            for d_idx, domain in enumerate(domains):
                # Map target_k back to [-1, 1]
                target_k = domain_policies.get(domain, {}).get("target_k", 6) if isinstance(domain_policies, dict) else 6
                action[d_idx, 0] = (target_k - 2.0) / 10.0 * 2.0 - 1.0
                
                # Map compute_scale back to [-1, 1]
                compute_scale = domain_policies.get(domain, {}).get("compute_scale", 1.0) if isinstance(domain_policies, dict) else 1.0
                action[d_idx, 1] = (compute_scale - 0.25) / 4.75 * 2.0 - 1.0
                
                # Map mutation_mult back to [-1, 1]
                mutation_mult = domain_policies.get(domain, {}).get("mutation_rate_mult", 1.0) if isinstance(domain_policies, dict) else 1.0
                action[d_idx, 2] = (mutation_mult - 0.25) / 3.75 * 2.0 - 1.0
                
                # Suffix bias
                action[d_idx, 3] = domain_policies.get(domain, {}).get("suffix_bias_delta", 0.0) if isinstance(domain_policies, dict) else 0.0
                
                # Elitism delta
                action[d_idx, 4] = (domain_policies.get(domain, {}).get("elitism_delta", 0.0) if isinstance(domain_policies, dict) else 0.0) / 0.2
                
        # 3. Reconstruct next_state at cycle T+1 from next_outcome_json
        next_state = np.zeros((6, 8), dtype=np.float32)
        if next_outcome_json:
            if isinstance(next_outcome_json, str):
                next_outcome = json.loads(next_outcome_json)
            else:
                next_outcome = next_outcome_json
                
            for d_idx, domain in enumerate(domains):
                domain_metrics = next_outcome.get(domain, {})
                next_state[d_idx, 0] = domain_metrics.get("k_used", 6) / 12.0
                next_state[d_idx, 1] = domain_metrics.get("mean_fitness", 0.1)
                next_state[d_idx, 2] = domain_metrics.get("max_fitness", 0.1)
                next_state[d_idx, 3] = (domain_metrics.get("silhouette", 0.0) + 1.0) / 2.0
                next_state[d_idx, 4] = domain_metrics.get("novelty_trend", 0.2)
                next_state[d_idx, 5] = domain_metrics.get("stagnation_chunks", 0.0) / 10.0
                next_state[d_idx, 6] = domain_metrics.get("verified_count", 0.0)
                next_state[d_idx, 7] = domain_metrics.get("lake_passed", 0.0)
        else:
            for d_idx in range(6):
                next_state[d_idx] = [0.5, 0.1, 0.1, 0.5, 0.2, 0.0, 0.0, 0.0]
                
        # 4. Compute reward from next_state
        rewards = []
        for d_idx in range(6):
            verified = next_state[d_idx, 6]
            max_fitness = next_state[d_idx, 2]
            novelty = next_state[d_idx, 4]
            silhouette = next_state[d_idx, 3]
            stagnation = next_state[d_idx, 5]
            compute_scale = (action[d_idx, 1] + 1.0) / 2.0 * 4.75 + 0.25
            
            island_reward = (
                5.0 * verified +
                1.0 * max_fitness +
                0.5 * novelty +
                0.3 * silhouette -
                0.5 * stagnation -
                0.1 * compute_scale
            )
            rewards.append(island_reward)
            
        total_reward = sum(rewards)
        
        transitions.append({
            "state": state.flatten().tolist(),
            "action": action.flatten().tolist(),
            "reward": float(total_reward),
            "next_state": next_state.flatten().tolist(),
            "done": False
        })
        
    cur.close()
    conn.close()
    return transitions
