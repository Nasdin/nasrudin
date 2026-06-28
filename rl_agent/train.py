import os
import torch
from env import NasrudinEnv
from world_model import WorldModel, train_world_model
from grpo_policy import GRPOPolicy, train_grpo_in_imagination
from database import fetch_historical_transitions
import numpy as np

def train_agent():
    print("=== SOTA Model-Based RL (GRPO-style) Training Pipeline ===")
    
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
    if os.path.exists("models/nasrudin_world_model.pt"):
        try:
            world_model.load_state_dict(torch.load("models/nasrudin_world_model.pt"))
            print("Successfully loaded existing World Model weights for fine-tuning.")
        except Exception as e:
            print(f"Could not load World Model: {e}. Starting fresh.")
            
    train_world_model(world_model, transitions, epochs=40, batch_size=64)
    
    # 3. Train the GRPO Policy inside the World Model's imagination!
    print("Initializing SOTA GRPO Policy inside the World Model's imagination...")
    policy = GRPOPolicy()
    if os.path.exists("models/nasrudin_grpo.pt"):
        try:
            policy.load_state_dict(torch.load("models/nasrudin_grpo.pt"))
            print("Successfully loaded existing GRPO Policy weights for fine-tuning.")
        except Exception as e:
            print(f"Could not load GRPO Policy: {e}. Starting fresh.")
            
    print("Training SOTA GRPO Policy inside imagination...")
    train_grpo_in_imagination(
        policy, 
        world_model, 
        transitions, 
        epochs=30, 
        group_size=16, 
        lr=1e-4, 
        beta=0.01
    )
    
    print("SOTA GRPO Policy trained inside imagination and saved successfully to models/nasrudin_grpo.pt!")

if __name__ == "__main__":
    train_agent()
