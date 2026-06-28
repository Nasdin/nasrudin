import gymnasium as gym
from gymnasium import spaces
import numpy as np

class NasrudinEnv(gym.Env):
    """
    Custom Gymnasium environment simulating the Nasrudin GA island discovery dynamics.
    
    State (Observation Space): 48 dimensions (6 islands * 8 features per island)
    Features per island:
      1. k_used (normalized to [0, 1])
      2. mean_fitness (in [0, 1])
      3. max_fitness (in [0, 1])
      4. silhouette (in [0, 1])
      5. novelty_trend (in [0, 1])
      6. stagnation_chunks (in [0, 1])
      7. verified_count (normalized)
      8. lake_pass_rate (in [0, 1])
      
    Action Space: 30 dimensions (6 islands * 5 continuous parameters in [-1, 1])
    Parameters per island:
      1. Target K (mapped to [2, 12])
      2. Compute scale multiplier (mapped to [0.25, 5.0])
      3. Mutation rate multiplier (mapped to [0.25, 4.0])
      4. Suffix bias delta (mapped to [-1.0, 1.0])
      5. Elitism delta (mapped to [-0.2, 0.2])
    """
    metadata = {"render_modes": ["human"]}

    def __init__(self, max_steps=100):
        super().__init__()
        self.max_steps = max_steps
        self.current_step = 0
        
        # 6 islands, 8 features each
        self.observation_space = spaces.Box(
            low=0.0, high=1.0, shape=(48,), dtype=np.float32
        )
        
        # 6 islands, 5 actions each
        self.action_space = spaces.Box(
            low=-1.0, high=1.0, shape=(30,), dtype=np.float32
        )
        
        # Optimal parameters per domain (hidden ground truth for simulation)
        # Domains: SR, EM, QM, Thermo, Classical, GR
        self.optimal_k = [4, 6, 8, 5, 3, 10]
        self.optimal_mutation = [1.0, 1.2, 1.5, 0.8, 0.5, 2.0]
        
        self.reset()

    def reset(self, seed=None, options=None):
        super().reset(seed=seed)
        self.current_step = 0
        
        # Initialize state with reasonable defaults
        # 6 islands * 8 features
        self.state = np.zeros((6, 8), dtype=np.float32)
        for i in range(6):
            self.state[i, 0] = 6.0 / 12.0  # k_used
            self.state[i, 1] = 0.1          # mean_fitness
            self.state[i, 2] = 0.1          # max_fitness
            self.state[i, 3] = 0.5          # silhouette
            self.state[i, 4] = 0.2          # novelty_trend
            self.state[i, 5] = 0.0          # stagnation_chunks
            self.state[i, 6] = 0.0          # verified_count
            self.state[i, 7] = 0.0          # lake_pass_rate
            
        return self.state.flatten(), {}

    def step(self, action):
        self.current_step += 1
        action = np.clip(action, -1.0, 1.0).reshape((6, 5))
        
        rewards = []
        new_state = self.state.copy()
        
        for i in range(6):
            # Map actions to physical parameters
            target_k = int(np.round(((action[i, 0] + 1.0) / 2.0) * 10.0 + 2.0)) # [2, 12]
            compute_scale = ((action[i, 1] + 1.0) / 2.0) * 4.75 + 0.25         # [0.25, 5.0]
            mutation_mult = ((action[i, 2] + 1.0) / 2.0) * 3.75 + 0.25         # [0.25, 4.0]
            suffix_bias = action[i, 3]                                         # [-1.0, 1.0]
            elitism_delta = action[i, 4] * 0.2                                 # [-0.2, 0.2]
            
            # Simulate dynamics
            # 1. Silhouette is maximized when target_k is close to optimal_k
            k_diff = abs(target_k - self.optimal_k[i])
            silhouette = max(0.0, 1.0 - (k_diff / 10.0))
            
            # 2. Novelty trend is driven by mutation rate and compute scale
            novelty = min(1.0, 0.2 + 0.5 * mutation_mult * (compute_scale ** 0.5))
            
            # 3. Stagnation chunks increase if mutation is too low or elitism is too high
            stagnation = max(0.0, min(1.0, self.state[i, 5] + 0.1 * (1.0 / (mutation_mult + 0.1)) + 0.2 * elitism_delta - 0.05 * compute_scale))
            
            # 4. Fitness growth is driven by compute scale, suffix bias, and balanced mutation
            # High stagnation or extremely high mutation hurts fitness growth
            mutation_penalty = abs(mutation_mult - self.optimal_mutation[i])
            growth_rate = 0.05 * compute_scale * (1.0 - 0.5 * stagnation) * (1.0 - 0.2 * mutation_penalty)
            
            mean_fitness = min(1.0, self.state[i, 1] + growth_rate)
            max_fitness = min(1.0, self.state[i, 2] + growth_rate * 1.5 + 0.05 * max(0.0, suffix_bias))
            
            # 5. Verified count (discoveries) has a probability of triggering when max_fitness is high
            discovery_prob = (max_fitness ** 3) * (1.0 - stagnation) * (silhouette ** 0.5)
            verified = 1.0 if np.random.random() < discovery_prob else 0.0
            
            # 6. Lake pass rate is high when silhouette and max_fitness are high
            lake_pass_rate = max_fitness * silhouette
            
            # Update state
            new_state[i, 0] = target_k / 12.0
            new_state[i, 1] = mean_fitness
            new_state[i, 2] = max_fitness
            new_state[i, 3] = silhouette
            new_state[i, 4] = novelty
            new_state[i, 5] = stagnation
            new_state[i, 6] = verified
            new_state[i, 7] = lake_pass_rate
            
            # Compute reward for this island
            # Reward components:
            # - Verified discovery (huge bonus)
            # - Max fitness (climbing the ladder)
            # - Novelty (exploring new areas)
            # - Silhouette (clustering quality)
            # - Penalties for stagnation and excessive compute cost
            island_reward = (
                5.0 * verified +
                1.0 * max_fitness +
                0.5 * novelty +
                0.3 * silhouette -
                0.5 * stagnation -
                0.1 * compute_scale  # Cost penalty
            )
            rewards.append(island_reward)
            
        self.state = new_state
        total_reward = sum(rewards)
        
        # Check termination
        terminated = self.current_step >= self.max_steps
        truncated = False
        
        return self.state.flatten(), total_reward, terminated, truncated, {}

    def render(self):
        print(f"Step {self.current_step}: Mean Fitness = {self.state[:, 1].mean():.4f}, Max Fitness = {self.state[:, 2].mean():.4f}, Verified = {self.state[:, 6].sum()}")
