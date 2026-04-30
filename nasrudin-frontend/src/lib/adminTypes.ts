/** Admin-only response shapes. Mirrors `crates/api/src/handlers/admin/*`. */

export interface AdminUser {
  id: string;
  email: string;
  display_name: string | null;
  plan_tier: string;
  research_credits: number;
  is_admin: boolean;
  is_trusted: boolean;
  spot_check_rate: number | null;
  created_at: string;
  stripe_customer_id: string | null;
}

export interface AdminUserDetail {
  user: AdminUser & {
    stripe_subscription_id: string | null;
    current_period_end: string | null;
    firebase_uid: string;
  };
  api_keys: AdminApiKey[];
  recent_audit: AuditEntry[];
}

export interface AdminApiKey {
  id: string;
  user_id: string | null;
  kind: string;
  name: string;
  prefix: string;
  last_used_at: string | null;
  expires_at: string | null;
  created_at: string;
  revoked_at: string | null;
  trust_override: boolean | null;
  spot_check_rate: number | null;
}

export interface AuditEntry {
  id: string;
  actor_user_id: string;
  target_user_id: string | null;
  action: string;
  before_value: unknown;
  after_value: unknown;
  reason: string;
  impersonating_user_id: string | null;
  request_ip: string | null;
  user_agent: string | null;
  created_at: string;
}

export interface BulkRun {
  id: string;
  started_by_admin_id: string;
  action: string;
  params: unknown;
  total_count: number;
  completed_count: number;
  failed_count: number;
  status: string;
  started_at: string;
  completed_at: string | null;
  failures: unknown;
}

export interface AdminStats {
  users_total: number;
  admins_count: number;
  trusted_users: number;
  theorems_by_status: Record<string, number>;
  reverify_queue_depth: number;
  lake_promotion_queue_depth: number;
  recent_audit: AuditEntry[];
}

export type BulkActionInput =
  | { action: 'set_trust'; params: { is_trusted: boolean } }
  | { action: 'set_plan'; params: { plan_tier: string } }
  | { action: 'adjust_credits'; params: { delta: number } }
  | { action: 'set_spot_check_rate'; params: { rate: number | null } };
