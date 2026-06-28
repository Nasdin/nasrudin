import os
import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np

class WorldModel(nn.Module):
    """
    Dreamer-style Latent World Model for Nasrudin.
    Predicts the next state (48-dim) and reward (1-dim) given the current state and action.
    """
    def __init__(self, state_dim=48, action_dim=30, hidden_dim=256):
        super().__init__()
        self.network = nn.Sequential(
            nn.Linear(state_dim + action_dim, hidden_dim),
            nn.LayerNorm(hidden_dim),
            nn.SiLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.LayerNorm(hidden_dim),
            nn.SiLU(),
        )
        # State predictor (outputs mean and log_std for Gaussian state representation)
        self.state_mean = nn.Linear(hidden_dim, state_dim)
        self.state_log_std = nn.Linear(hidden_dim, state_dim)
        
        # Reward predictor
        self.reward_pred = nn.Linear(hidden_dim, 1)

    def forward(self, state, action):
        x = torch.cat([state, action], dim=-1)
        features = self.network(x)
        
        mean = self.state_mean(features)
        log_std = torch.clamp(self.state_log_std(features), -20, 2)
        std = torch.exp(log_std)
        
        reward = self.reward_pred(features)
        return mean, std, reward

    def predict(self, state, action):
        """
        Deterministic prediction for environment simulation.
        """
        self.eval()
        with torch.no_grad():
            state_t = torch.FloatTensor(state)
            action_t = torch.FloatTensor(action)
            mean, _, reward = self.forward(state_t, action_t)
            return mean.numpy(), reward.numpy()

def train_world_model(world_model, transitions, epochs=50, batch_size=64, lr=1e-3):
    """
    Train the World Model on historical database transitions using supervised learning.
    """
    world_model.train()
    optimizer = optim.AdamW(world_model.parameters(), lr=lr, weight_decay=1e-4)
    criterion_mse = nn.MSELoss()
    
    states = torch.FloatTensor([t["state"] for t in transitions])
    actions = torch.FloatTensor([t["action"] for t in transitions])
    rewards = torch.FloatTensor([[t["reward"]] for t in transitions])
    next_states = torch.FloatTensor([t["next_state"] for t in transitions])
    
    dataset = torch.utils.data.TensorDataset(states, actions, rewards, next_states)
    loader = torch.utils.data.DataLoader(dataset, batch_size=batch_size, shuffle=True)
    
    print(f"Training World Model on {len(transitions)} transitions for {epochs} epochs...")
    for epoch in range(epochs):
        epoch_loss = 0.0
        for batch_s, batch_a, batch_r, batch_ns in loader:
            optimizer.zero_grad()
            
            mean, std, pred_r = world_model(batch_s, batch_a)
            
            # Loss = State prediction loss (negative log likelihood) + Reward prediction loss
            # For simplicity and stability, we use MSE for both state and reward prediction
            loss_state = criterion_mse(mean, batch_ns)
            loss_reward = criterion_mse(pred_r, batch_r)
            
            loss = loss_state + loss_reward
            loss.backward()
            optimizer.step()
            
            epoch_loss += loss.item()
            
        if (epoch + 1) % 10 == 0 or epoch == 0:
            print(f"Epoch {epoch+1}/{epochs} - Loss: {epoch_loss/len(loader):.6f}")
            
    # Save the trained World Model
    os.makedirs("models", exist_ok=True)
    torch.save(world_model.state_state_dict() if hasattr(world_model, "state_state_dict") else world_model.state_dict(), "models/nasrudin_world_model.pt")
    print("World Model saved successfully to models/nasrudin_world_model.pt!")
