import os
import torch
from stable_baselines3 import PPO
from stable_baselines3.common.env_util import make_vec_env
from env import NasrudinEnv, DreamerEnv
from world_model import WorldModel, train_world_model
from database import fetch_historical_transitions

def train_agent(total_timesteps=50000):
    print("=== SOTA Model-Based RL (Dreamer-style) Training Pipeline ===")
    
    # 1. Fetch historical transitions from the database
    transitions = []
    try:
        transitions = fetch_historical_transitions()
        print(f"Successfully fetched {len(transitions)} transitions from the database.")
    except Exception as e:
        print(f"Error fetching transitions: {e}. Using simulated transitions for bootstrapping.")
        
    # If no transitions exist yet, bootstrap with simulated transitions from NasrudinEnv
    if not transitions:
        print("No historical transitions found. Bootstrapping with simulated transitions...")
        env = NasrudinEnv()
        for _ in range(100):
            state, _ = env.reset()
            for _ in range(100):
                action = env.action_space.sample()
                next_state, reward, terminated, _, _ = env.step(action)
                transitions.append({
                    "state": state.tolist(),
                    "action": action.tolist(),
                    "reward": reward,
                    "next_state": next_state.tolist(),
                    "done": terminated
                })
                state = next_state
                if terminated:
                    break
                    
    # 2. Train the World Model (RSSM-style)
    world_model = WorldModel()
    train_world_model(world_model, transitions, epochs=50, batch_size=64)
    
    # 3. Create the vectorized Dreamer Environment (Imagination!)
    print("Initializing SOTA Dreamer Environment (Imagination)...")
    env = make_vec_env(lambda: DreamerEnv(max_steps=15), n_envs=4)
    
    # 4. Train the PPO Agent inside the World Model's imagination!
    print("Initializing SOTA PPO Agent inside the World Model's imagination...")
    model = PPO(
        "MlpPolicy",
        env,
        verbose=1,
        learning_rate=3e-4,
        n_steps=2048,
        batch_size=64,
        n_epochs=10,
        gamma=0.99,
        gae_lambda=0.95,
        clip_range=0.2,
        ent_coef=0.01,
        policy_kwargs=dict(net_arch=dict(pi=[128, 128], vf=[128, 128])),
        tensorboard_log="./ppo_nasrudin_tensorboard/"
    )
    
    print(f"Training SOTA PPO Agent inside imagination for {total_timesteps} timesteps...")
    model.learn(total_timesteps=total_timesteps)
    
    # Save the trained model
    os.makedirs("models", exist_ok=True)
    model.save("models/nasrudin_ppo")
    print("SOTA PPO Agent trained inside imagination and saved successfully to models/nasrudin_ppo.zip!")

if __name__ == "__main__":
    train_agent()
