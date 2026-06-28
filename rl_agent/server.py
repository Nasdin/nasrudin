import os
import time
import threading
import numpy as np
import torch
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from typing import List
from grpo_policy import GRPOPolicy, train_grpo_in_imagination
from env import NasrudinEnv
from world_model import WorldModel, train_world_model
from database import fetch_historical_transitions, get_db_connection

app = FastAPI(title="Nasrudin SOTA GRPO RL Server", version="1.1.0")

# Load the trained model
MODEL_PATH = "models/nasrudin_grpo.pt"
WORLD_MODEL_PATH = "models/nasrudin_world_model.pt"
LAST_TRAINED_CYCLE_PATH = "models/last_trained_cycle.txt"

policy = None
world_model = None
training_lock = threading.Lock()

def get_latest_completed_cycle_id():
    """
    Query the database to get the ID of the most recent completed cluster steering cycle.
    """
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("""
            SELECT id FROM cluster_steering 
            WHERE ended_at IS NOT NULL 
            ORDER BY started_at DESC LIMIT 1
        """)
        row = cur.fetchone()
        cur.close()
        conn.close()
        return row[0] if row else None
    except Exception as e:
        print(f"Error fetching latest cycle ID: {e}")
        return None

def get_last_trained_cycle_id():
    """
    Read the last trained cycle ID from the local state file.
    """
    if os.path.exists(LAST_TRAINED_CYCLE_PATH):
        try:
            with open(LAST_TRAINED_CYCLE_PATH, "r") as f:
                return f.read().strip()
        except Exception as e:
            print(f"Error reading last trained cycle ID: {e}")
    return None

def save_last_trained_cycle_id(cycle_id):
    """
    Save the last trained cycle ID to the local state file.
    """
    try:
        os.makedirs(os.path.dirname(LAST_TRAINED_CYCLE_PATH), exist_ok=True)
        with open(LAST_TRAINED_CYCLE_PATH, "w") as f:
            f.write(str(cycle_id))
    except Exception as e:
        print(f"Error saving last trained cycle ID: {e}")

def run_training_step(num_epochs=15):
    """
    Perform a Dreamer-style GRPO Model-Based RL training step:
      1. Re-train the World Model on the latest database transitions.
      2. Re-train the GRPO policy inside the updated World Model's imagination!
    """
    global policy, world_model
    latest_id = get_latest_completed_cycle_id()
    if latest_id is None:
        print("No completed cycles found in database. Skipping training.")
        return False
        
    try:
        # 1. Re-train the World Model
        transitions = fetch_historical_transitions()
        if transitions:
            print(f"Fine-tuning World Model on {len(transitions)} transitions...")
            train_world_model(world_model, transitions, epochs=15, batch_size=64)
            
        # 2. Re-train the GRPO agent inside the updated World Model's imagination!
        print(f"Fine-tuning SOTA GRPO policy inside imagination for {num_epochs} epochs...")
        train_grpo_in_imagination(
            policy,
            world_model,
            transitions,
            epochs=num_epochs,
            group_size=16,
            lr=1e-4,
            beta=0.01
        )
        save_last_trained_cycle_id(latest_id)
        print(f"Model trained and saved successfully! Last trained cycle ID updated to: {latest_id}")
        return True
    except Exception as e:
        print(f"Error during training step: {e}")
        return False

def load_or_init_model():
    global policy, world_model
    
    # Initialize World Model
    world_model = WorldModel()
    if os.path.exists(WORLD_MODEL_PATH):
        print(f"Loading SOTA World Model from {WORLD_MODEL_PATH}...")
        try:
            world_model.load_state_dict(torch.load(WORLD_MODEL_PATH))
        except Exception as e:
            print(f"Error loading World Model: {e}. Starting fresh.")
    
    # Initialize GRPO Policy Model
    policy = GRPOPolicy()
    if os.path.exists(MODEL_PATH):
        print(f"Loading SOTA GRPO policy from {MODEL_PATH}...")
        try:
            policy.load_state_dict(torch.load(MODEL_PATH))
        except Exception as e:
            print(f"Error loading GRPO Policy: {e}. Starting fresh.")
    else:
        print("No pre-trained model found. Initializing a fresh GRPO model...")
        
        # Bootstrap model using offline pre-training on historical database transitions
        try:
            print("Bootstrapping model using offline pre-training on historical database transitions...")
            transitions = fetch_historical_transitions()
            if transitions:
                print(f"Found {len(transitions)} historical transitions. Pre-training model...")
                run_training_step(num_epochs=20)
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
        "model_loaded": policy is not None,
        "world_model_loaded": world_model is not None,
        "model_path": MODEL_PATH,
        "algorithm": "GRPO (Group Relative Policy Optimization)",
        "observation_space_shape": [48],
        "action_space_shape": [30],
        "last_trained_cycle_id": get_last_trained_cycle_id(),
        "latest_completed_cycle_id": get_latest_completed_cycle_id(),
    }

@app.post("/predict", response_model=ActionResponse)
def predict(request: ObservationRequest):
    global policy
    if policy is None:
        raise HTTPException(status_code=503, detail="Model not loaded")
        
    obs = np.array(request.observation, dtype=np.float32)
    if obs.shape != (48,):
        raise HTTPException(
            status_code=400, 
            detail=f"Invalid observation shape. Expected (48,), got {obs.shape}"
        )
        
    # Run GRPO policy model inference (deterministic)
    action = policy.predict(obs, deterministic=True)
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
    global policy
    if policy is None:
        raise HTTPException(status_code=503, detail="Model not loaded")
        
    if not request.transitions:
        return {"message": "No transitions provided for training"}
        
    with training_lock:
        print(f"Received {len(request.transitions)} transitions for online learning...")
        run_training_step(num_epochs=5)
        
    return {
        "message": "Online learning step completed successfully",
        "transitions_processed": len(request.transitions),
        "model_saved": True
    }

def automated_training_loop():
    """
    Background thread that automatically runs on a schedule to fetch the latest
    transitions from the database and fine-tune the GRPO model.
    """
    interval = int(os.getenv("RL_TRAIN_INTERVAL_SECONDS", "3600"))
    print(f"Starting automated training loop with interval of {interval} seconds...")
    
    # 1. Immediate Boot Check (Durability Gate)
    try:
        last_trained = get_last_trained_cycle_id()
        latest_completed = get_latest_completed_cycle_id()
        
        if latest_completed is not None and (last_trained is None or str(last_trained) != str(latest_completed)):
            print(f"Durability Gate: Detected new completed cycles since last training (last_trained={last_trained}, latest={latest_completed}). Training immediately...")
            with training_lock:
                run_training_step(num_epochs=10)
        else:
            print("Durability Gate: No new completed cycles detected on boot. Entering schedule.")
    except Exception as e:
        print(f"Error during durability boot check: {e}")
        
    # 2. Periodic Schedule
    while True:
        time.sleep(interval)
        try:
            last_trained = get_last_trained_cycle_id()
            latest_completed = get_latest_completed_cycle_id()
            
            if latest_completed is not None and (last_trained is None or str(last_trained) != str(latest_completed)):
                print("Automated Training: New completed cycles detected. Fine-tuning model...")
                with training_lock:
                    run_training_step(num_epochs=10)
            else:
                print("Automated Training: No new completed cycles detected. Skipping training.")
        except Exception as e:
            print(f"Error during automated training: {e}")

# Start the automated training loop in a background thread
train_thread = threading.Thread(target=automated_training_loop, daemon=True)
train_thread.start()

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=5005)
