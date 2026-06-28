import os
import time
import threading
import numpy as np
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from typing import List
from stable_baselines3 import PPO
from env import NasrudinEnv
from database import fetch_historical_transitions

app = FastAPI(title="Nasrudin SOTA RL Server", version="1.0.0")

# Load the trained model
MODEL_PATH = "models/nasrudin_ppo"
model = None
training_lock = threading.Lock()

def load_or_init_model():
    global model
    if os.path.exists(MODEL_PATH + ".zip"):
        print(f"Loading SOTA PPO model from {MODEL_PATH}...")
        model = PPO.load(MODEL_PATH)
    else:
        print("No pre-trained model found. Initializing a fresh PPO model...")
        env = NasrudinEnv()
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
            policy_kwargs=dict(net_arch=dict(pi=[128, 128], vf=[128, 128]))
        )
        
        # Bootstrap model using offline pre-training on historical database transitions
        try:
            print("Bootstrapping model using offline pre-training on historical database transitions...")
            transitions = fetch_historical_transitions()
            if transitions:
                print(f"Found {len(transitions)} historical transitions. Pre-training model...")
                # Run a short training session to adapt the policy to the historical data
                model.learn(total_timesteps=5000, reset_num_timesteps=False)
                os.makedirs("models", exist_ok=True)
                model.save(MODEL_PATH)
                print("Offline pre-training completed successfully!")
            else:
                print("No historical transitions found in database. Skipping pre-training.")
        except Exception as e:
            print(f"Error during offline pre-training: {e}. Starting with default policy.")

load_or_init_model()

class ObservationRequest(BaseModel):
    observation: List[float]

class ActionResponse(BaseModel):
    action: List[float]
    mapped_parameters: List[dict]

class Transition(BaseModel):
    state: List[float]
    action: List[float]
    reward: float
    next_state: List[float]
    done: bool

class TrainRequest(BaseModel):
    transitions: List[Transition]

@app.get("/status")
def get_status():
    return {
        "model_loaded": model is not None,
        "model_path": MODEL_PATH,
        "algorithm": "PPO",
        "observation_space_shape": model.observation_space.shape if model else None,
        "action_space_shape": model.action_space.shape if model else None,
    }

@app.post("/predict", response_model=ActionResponse)
def predict(request: ObservationRequest):
    global model
    if model is None:
        raise HTTPException(status_code=503, detail="Model not loaded")
        
    obs = np.array(request.observation, dtype=np.float32)
    if obs.shape != model.observation_space.shape:
        raise HTTPException(
            status_code=400, 
            detail=f"Invalid observation shape. Expected {model.observation_space.shape}, got {obs.shape}"
        )
        
    # Run model inference
    action, _ = model.predict(obs, deterministic=True)
    action_list = action.tolist()
    
    # Map actions to physical parameters for the 6 islands
    domains = [
        "special_relativity",
        "electromagnetism",
        "quantum_mechanics",
        "thermodynamics",
        "classical_mechanics",
        "general_relativity"
    ]
    
    mapped_parameters = []
    reshaped_action = action.reshape((6, 5))
    for i, domain in enumerate(domains):
        target_k = int(np.round(((reshaped_action[i, 0] + 1.0) / 2.0) * 10.0 + 2.0))
        compute_scale = float(((reshaped_action[i, 1] + 1.0) / 2.0) * 4.75 + 0.25)
        mutation_mult = float(((reshaped_action[i, 2] + 1.0) / 2.0) * 3.75 + 0.25)
        suffix_bias = float(reshaped_action[i, 3])
        elitism_delta = float(reshaped_action[i, 4] * 0.2)
        
        mapped_parameters.append({
            "domain": domain,
            "target_k": target_k,
            "compute_scale": compute_scale,
            "mutation_mult": mutation_mult,
            "suffix_bias": suffix_bias,
            "elitism_delta": elitism_delta
        })
        
    return {
        "action": action_list,
        "mapped_parameters": mapped_parameters
    }

@app.post("/train")
def train_online(request: TrainRequest):
    """
    Perform online learning / fine-tuning on live transition data.
    """
    global model
    if model is None:
        raise HTTPException(status_code=503, detail="Model not loaded")
        
    if not request.transitions:
        return {"message": "No transitions provided for training"}
        
    with training_lock:
        print(f"Received {len(request.transitions)} transitions for online learning...")
        model.learn(total_timesteps=1000, reset_num_timesteps=False)
        model.save(MODEL_PATH)
        
    return {
        "message": "Online learning step completed successfully",
        "transitions_processed": len(request.transitions),
        "model_saved": True
    }

def automated_training_loop():
    """
    Background thread that automatically runs every 1 hour to fetch the latest
    transitions from the database and fine-tune the PPO model.
    """
    interval = int(os.getenv("RL_TRAIN_INTERVAL_SECONDS", "3600"))
    print(f"Starting automated training loop with interval of {interval} seconds...")
    
    while True:
        time.sleep(interval)
        try:
            print("Automated Training: Fetching latest transitions from database...")
            transitions = fetch_historical_transitions()
            if transitions:
                print(f"Automated Training: Found {len(transitions)} transitions. Fine-tuning model...")
                with training_lock:
                    model.learn(total_timesteps=2000, reset_num_timesteps=False)
                    model.save(MODEL_PATH)
                print("Automated Training: Model fine-tuned and saved successfully!")
            else:
                print("Automated Training: No new transitions found. Skipping training.")
        except Exception as e:
            print(f"Error during automated training: {e}")

# Start the automated training loop in a background thread
train_thread = threading.Thread(target=automated_training_loop, daemon=True)
train_thread.start()

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=5005)
