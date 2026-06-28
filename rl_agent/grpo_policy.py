import os
import torch
import torch.nn as nn
import torch.optim as optim
import torch.nn.functional as F
import numpy as np

class GRPOPolicy(nn.Module):
    """
    SOTA Group Relative Policy Optimization (GRPO) continuous action controller.
    Uses continuous Gaussian policies with Tanh squashing for bounded [-1, 1] actions.
    Eliminates the separate value network, optimizing relative advantages within a group.
    """
    def __init__(self, state_dim=48, action_dim=30, hidden_dim=256):
        super().__init__()
        self.network = nn.Sequential(
            nn.Linear(state_dim, hidden_dim),
            nn.LayerNorm(hidden_dim),
            nn.SiLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.LayerNorm(hidden_dim),
            nn.SiLU(),
        )
        self.action_mean = nn.Linear(hidden_dim, action_dim)
        # Learnable log standard deviation per action (independent of state for stability)
        self.action_log_std = nn.Parameter(torch.zeros(action_dim) - 0.5)

    def forward(self, state):
        features = self.network(state)
        mean = self.action_mean(features)
        # Clamp log_std to prevent numerical instability
        log_std = torch.clamp(self.action_log_std, -20, 2)
        std = torch.exp(log_std).expand_as(mean)
        return mean, std

    def sample_group(self, state, group_size=8):
        """
        Sample a group of actions for GRPO relative advantage estimation.
        Returns actions in [-1, 1] and their log probabilities.
        """
        mean, std = self.forward(state)  # mean: [B, action_dim], std: [B, action_dim]
        
        # Expand state to batch x group_size
        # mean: [B, G, action_dim]
        mean_exp = mean.unsqueeze(1).expand(-1, group_size, -1)
        std_exp = std.unsqueeze(1).expand(-1, group_size, -1)
        
        normal = torch.distributions.Normal(mean_exp, std_exp)
        raw_actions = normal.rsample()  # Reparameterization trick
        
        # Tanh squashing to bound actions in [-1, 1]
        actions = torch.tanh(raw_actions)
        
        # Compute log prob with Tanh change-of-variables correction
        # log_prob = log_prob_normal - sum(log(1 - tanh(x)^2))
        log_probs = normal.log_prob(raw_actions) - torch.log(1.0 - actions.pow(2) + 1e-6)
        log_probs = log_probs.sum(dim=-1)  # Sum over action dimensions -> [B, G]
        
        return actions, log_probs, raw_actions

    def compute_log_prob(self, state, actions):
        """
        Compute log probability of specific actions (for policy ratio).
        Supports backpropagation.
        """
        mean, std = self.forward(state)
        normal = torch.distributions.Normal(mean, std)
        
        # Invert Tanh to get raw actions
        # raw_actions = artanh(actions)
        # artanh(x) = 0.5 * log((1+x)/(1-x))
        clamped_actions = torch.clamp(actions, -0.9999, 0.9999)
        raw_actions = 0.5 * torch.log((1.0 + clamped_actions) / (1.0 - clamped_actions))
        
        log_probs = normal.log_prob(raw_actions) - torch.log(1.0 - clamped_actions.pow(2) + 1e-6)
        return log_probs.sum(dim=-1)

    def predict(self, state, deterministic=True):
        """
        Inference prediction.
        """
        self.eval()
        with torch.no_grad():
            state_t = torch.FloatTensor(state)
            mean, _ = self.forward(state_t)
            if deterministic:
                action = torch.tanh(mean)
            else:
                normal = torch.distributions.Normal(mean, torch.exp(self.action_log_std))
                action = torch.tanh(normal.sample())
            return action.numpy()

def train_grpo_in_imagination(policy, world_model, transitions, epochs=10, group_size=16, lr=1e-4, beta=0.01, clip_eps=0.2):
    """
    SOTA Group Relative Policy Optimization (GRPO) training in Imagination.
    
    For each state in historical transitions:
      1. Sample a group of G actions from current policy.
      2. Use the World Model to predict the returns of these actions.
      3. Compute relative advantages within the group.
      4. Optimize the policy with relative surrogate loss and KL divergence constraint.
    """
    policy.train()
    world_model.eval()
    
    # Save old policy for KL divergence target
    old_policy = GRPOPolicy()
    old_policy.load_state_dict(policy.state_dict())
    old_policy.eval()
    
    optimizer = optim.AdamW(policy.parameters(), lr=lr, weight_decay=1e-4)
    
    # Extract unique states from transitions to imagine from
    states = torch.FloatTensor([t["state"] for t in transitions])
    dataset = torch.utils.data.TensorDataset(states)
    loader = torch.utils.data.DataLoader(dataset, batch_size=32, shuffle=True)
    
    print(f"Training GRPO Policy in Imagination on {len(states)} state-anchors (group_size={group_size})...")
    
    for epoch in range(epochs):
        epoch_policy_loss = 0.0
        epoch_kl = 0.0
        
        for (batch_s,) in loader:
            optimizer.zero_grad()
            
            # 1. Sample group of G actions from current policy
            # actions: [B, G, action_dim], log_probs: [B, G], raw_actions: [B, G, action_dim]
            actions, log_probs, raw_actions = policy.sample_group(batch_s, group_size=group_size)
            
            # 2. Sample same group from old policy to compute importance ratio
            with torch.no_grad():
                # Re-evaluate log_probs under old policy
                mean_old, std_old = old_policy(batch_s)
                mean_old_exp = mean_old.unsqueeze(1).expand(-1, group_size, -1)
                std_old_exp = std_old.unsqueeze(1).expand(-1, group_size, -1)
                normal_old = torch.distributions.Normal(mean_old_exp, std_old_exp)
                
                log_probs_old = normal_old.log_prob(raw_actions) - torch.log(1.0 - actions.pow(2) + 1e-6)
                log_probs_old = log_probs_old.sum(dim=-1)  # [B, G]
                
            # 3. Evaluate returns inside the World Model (3-step imagination rollout)
            with torch.no_grad():
                B, G, A = actions.shape
                # Flatten batch and group for parallel evaluation in World Model
                flat_s = batch_s.unsqueeze(1).expand(-1, group_size, -1).reshape(B * G, -1)
                flat_a = actions.reshape(B * G, -1)
                
                # Rollout 3 steps
                discounted_returns = torch.zeros(B * G)
                gamma = 0.9
                
                current_s = flat_s
                current_a = flat_a
                
                for step in range(3):
                    # Predict next state and reward
                    pred_ns_mean, _, pred_r = world_model(current_s, current_a)
                    discounted_returns += (gamma ** step) * pred_r.squeeze(-1)
                    
                    # Next state becomes current state
                    current_s = pred_ns_mean
                    # Sample next action from old policy to keep rollouts realistic
                    mean_next, std_next = old_policy(current_s)
                    normal_next = torch.distributions.Normal(mean_next, std_next)
                    current_a = torch.tanh(normal_next.sample())
                
                # Reshape returns back to [B, G]
                returns = discounted_returns.reshape(B, G)
                
            # 4. Compute Relative Advantages within the group
            mean_returns = returns.mean(dim=-1, keepdim=True)
            std_returns = returns.std(dim=-1, keepdim=True) + 1e-6
            advantages = (returns - mean_returns) / std_returns  # [B, G]
            
            # 5. GRPO Loss computation
            # Importance ratios
            ratios = torch.exp(log_probs - log_probs_old)  # [B, G]
            
            # Clipped surrogate objective
            surr1 = ratios * advantages
            surr2 = torch.clamp(ratios, 1.0 - clip_eps, 1.0 + clip_eps) * advantages
            policy_loss = -torch.min(surr1, surr2).mean()
            
            # KL divergence constraint penalty: D_KL(pi_theta || pi_old)
            # Continuous Gaussian KL formula: log(std_old/std) + (std^2 + (mean-mean_old)^2)/(2*std_old^2) - 0.5
            mean, std = policy(batch_s)
            kl_div = torch.log(std_old / std) + (std.pow(2) + (mean - mean_old).pow(2)) / (2.0 * std_old.pow(2)) - 0.5
            kl_loss = kl_div.sum(dim=-1).mean()
            
            loss = policy_loss + beta * kl_loss
            loss.backward()
            
            # Gradient clipping for extreme stability
            torch.nn.utils.clip_grad_norm_(policy.parameters(), max_norm=0.5)
            optimizer.step()
            
            epoch_policy_loss += policy_loss.item()
            epoch_kl += kl_loss.item()
            
        if (epoch + 1) % 5 == 0 or epoch == 0:
            print(f"GRPO Epoch {epoch+1}/{epochs} - Policy Loss: {epoch_policy_loss/len(loader):.6f} - KL Div: {epoch_kl/len(loader):.6f}")
            
    # Save the policy model
    os.makedirs("models", exist_ok=True)
    torch.save(policy.state_dict(), "models/nasrudin_grpo.pt")
    print("GRPO Policy saved successfully to models/nasrudin_grpo.pt!")
