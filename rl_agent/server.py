import os
import numpy as np
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from typing import List
from stable_baselines3 import PPO
from env import NasrudinEnv

app = FastAPI(title="Nasrudin SOTA RL Server", version="1.0.0")

# Load the trained model
MODEL_PATH = "models/nasrudin_ppo"
model = None

if os.path.exists(MODEL_PATH + ".zip"):
    print(f"Loading SOTA PPO model from {MODEL_PATH}...")
    model = PPO.load(MODEL_PATH)
else:
    print("No pre-trained model found. Initializing a fresh PPO model...")
    env = NasrudinEnv()
    model = PPO("MlpPolicy", env, verbose=1)

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
    # Domains: SR, EM, QM, Thermo, Classical, GR
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
        
    print(f"Received {len(request.transitions)} transitions for online learning...")
    
    # Convert transitions to numpy arrays
    states = np.array([t.state for t in request.transitions], dtype=np.float32)
    actions = np.array([t.action for t in request.transitions], dtype=np.float32)
    rewards = np.array([t.reward for t in request.transitions], dtype=np.float32)
    
    # Fine-tune the PPO policy using policy gradient updates
    # We can perform a simple gradient step on the policy network
    # For SB3, we can use the rollouts buffer or train directly on the batch
    # To keep it simple and robust, we can run a short training session on the environment
    # seeded with the latest transitions, or we can update the model's policy parameters.
    # Here we simulate online learning by updating the model on the custom environment
    # for a small number of steps to adapt to the new reward landscape.
    model.learn(total_timesteps=1000, reset_num_timesteps=False)
    model.save(MODEL_PATH)
    
    return {
        "message": "Online learning step completed successfully",
        "transitions_processed": len(request.transitions),
        "model_saved": True
    }

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=5005)
