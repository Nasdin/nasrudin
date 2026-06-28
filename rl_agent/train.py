import os
from stable_baselines3 import PPO
from stable_baselines3.common.env_util import make_vec_env
from env import NasrudinEnv

def train_agent(total_timesteps=50000):
    print("Initializing Nasrudin Gymnasium environment...")
    # Create vectorized environment for faster training
    env = make_vec_env(lambda: NasrudinEnv(max_steps=100), n_envs=4)
    
    print("Initializing SOTA PPO Agent...")
    # SOTA PPO with custom policy architecture
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
    
    print(f"Training SOTA PPO Agent for {total_timesteps} timesteps...")
    model.learn(total_timesteps=total_timesteps)
    
    # Save the trained model
    os.makedirs("models", exist_ok=True)
    model.save("models/nasrudin_ppo")
    print("SOTA PPO Agent trained and saved successfully to models/nasrudin_ppo.zip!")

if __name__ == "__main__":
    train_agent()
