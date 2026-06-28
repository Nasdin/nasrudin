import os
import gymnasium as gym
from gymnasium import spaces
import numpy as np
import torch
from world_model import WorldModel

class NasrudinEnv(gym.Env):
    """
    Custom Gymnasium environment simulating the Nasrudin GA island discovery dynamics.
    """
    metadata = {"render_modes": ["human"]}

    def __init__(self, max_steps=100):
        super().__init__()
        self.max_steps = max_steps
        self.current_step = 0
        
        self.observation_space = spaces.Box(
            low=0.0, high=1.0, shape=(48,), dtype=np.float32
        )
        self.action_space = spaces.Box(
            low=-1.0, high=1.0, shape=(30,), dtype=np.float32
        )
        
        self.optimal_k = [4, 6, 8, 5, 3, 10]
        self.optimal_mutation = [1.0, 1.2, 1.5, 0.8, 0.5, 2.0]
        self.reset()

    def reset(self, seed=None, options=None):
        super().reset(seed=seed)
        self.current_step = 0
        self.state = np.zeros((6, 8), dtype=np.float32)
        for i in range(6):
            self.state[i, 0] = 6.0 / 12.0
            self.state[i, 1] = 0.1
            self.state[i, 2] = 0.1
            self.state[i, 3] = 0.5
            self.state[i, 4] = 0.2
            self.state[i, 5] = 0.0
            self.state[i, 6] = 0.0
            self.state[i, 7] = 0.0
        return self.state.flatten(), {}

    def step(self, action):
        self.current_step += 1
        action = np.clip(action, -1.0, 1.0).reshape((6, 5))
        
        rewards = []
        new_state = self.state.copy()
        
        for i in range(6):
            target_k = int(np.round(((action[i, 0] + 1.0) / 2.0) * 10.0 + 2.0))
            compute_scale = ((action[i, 1] + 1.0) / 2.0) * 4.75 + 0.25
            mutation_mult = ((action[i, 2] + 1.0) / 2.0) * 3.75 + 0.25
            suffix_bias = action[i, 3]
            elitism_delta = action[i, 4] * 0.2
            
            k_diff = abs(target_k - self.optimal_k[i])
            silhouette = max(0.0, 1.0 - (k_diff / 10.0))
            novelty = min(1.0, 0.2 + 0.5 * mutation_mult * (compute_scale ** 0.5))
            stagnation = max(0.0, min(1.0, self.state[i, 5] + 0.1 * (1.0 / (mutation_mult + 0.1)) + 0.2 * elitism_delta - 0.05 * compute_scale))
            
            mutation_penalty = abs(mutation_mult - self.optimal_mutation[i])
            growth_rate = 0.05 * compute_scale * (1.0 - 0.5 * stagnation) * (1.0 - 0.2 * mutation_penalty)
            
            mean_fitness = min(1.0, self.state[i, 1] + growth_rate)
            max_fitness = min(1.0, self.state[i, 2] + growth_rate * 1.5 + 0.05 * max(0.0, suffix_bias))
            
            discovery_prob = (max_fitness ** 3) * (1.0 - stagnation) * (silhouette ** 0.5)
            verified = 1.0 if np.random.random() < discovery_prob else 0.0
            lake_pass_rate = max_fitness * silhouette
            
            new_state[i, 0] = target_k / 12.0
            new_state[i, 1] = mean_fitness
            new_state[i, 2] = max_fitness
            new_state[i, 3] = silhouette
            new_state[i, 4] = novelty
            new_state[i, 5] = stagnation
            new_state[i, 6] = verified
            new_state[i, 7] = lake_pass_rate
            
            island_reward = (
                5.0 * verified +
                1.0 * max_fitness +
                0.5 * novelty +
                0.3 * silhouette -
                0.5 * stagnation -
                0.1 * compute_scale
            )
            rewards.append(island_reward)
            
        self.state = new_state
        total_reward = sum(rewards)
        
        terminated = self.current_step >= self.max_steps
        truncated = False
        return self.state.flatten(), total_reward, terminated, truncated, {}

class DreamerEnv(gym.Env):
    """
    SOTA Model-Based RL Imagination Environment.
    Simulates transitions entirely inside the trained World Model's "imagination".
    Allows the agent to train on millions of virtual steps in milliseconds!
    """
    def __init__(self, world_model_path="models/nasrudin_world_model.pt", max_steps=15):
        super().__init__()
        self.max_steps = max_steps
        self.current_step = 0
        
        self.observation_space = spaces.Box(
            low=0.0, high=1.0, shape=(48,), dtype=np.float32
        )
        self.action_space = spaces.Box(
            low=-1.0, high=1.0, shape=(30,), dtype=np.float32
        )
        
        # Load the World Model
        self.world_model = WorldModel()
        if os.path.exists(world_model_path):
            self.world_model.load_state_dict(torch.load(world_model_path))
        self.world_model.eval()
        
        self.reset()

    def reset(self, seed=None, options=None):
        super().reset(seed=seed)
        self.current_step = 0
        # Start from a random realistic state
        self.state = np.random.uniform(0.1, 0.5, size=(48,)).astype(np.float32)
        return self.state, {}

    def step(self, action):
        self.current_step += 1
        action = np.clip(action, -1.0, 1.0).astype(np.float32)
        
        # Predict next state and reward using the World Model (Imagination step!)
        next_state, reward = self.world_model.predict(self.state, action)
        
        self.state = np.clip(next_state, 0.0, 1.0)
        
        terminated = self.current_step >= self.max_steps
        truncated = False
        return self.state, float(reward.item()), terminated, truncated, {}
