// Based on Kovrin SchemaExporter output
// Dashboard-adjusted: fields always present from API are non-optional

export type RiskLevel = 'LOW' | 'MEDIUM' | 'HIGH' | 'CRITICAL'
export type TaskStatus = 'PENDING' | 'READY' | 'EXECUTING' | 'COMPLETED' | 'FAILED' | 'REJECTED_BY_L0' | 'AWAITING_HUMAN' | 'SKIPPED'
export type SpeculationTier = 'FREE' | 'GUARDED' | 'NONE'
export type RoutingAction = 'AUTO_EXECUTE' | 'SANDBOX_REVIEW' | 'HUMAN_APPROVAL'
export type ContainmentLevel = 'WARN' | 'PAUSE' | 'KILL'
export type AgentRole = 'RESEARCHER' | 'WRITER' | 'REVIEWER' | 'PLANNER' | 'SPECIALIST'
export type ApprovalStatus = 'PENDING' | 'APPROVED' | 'REJECTED' | 'TIMEOUT'
export type ViewMode = 'OPERATOR' | 'ANALYST' | 'DEVELOPER'
export type AutonomyProfile = 'DEFAULT' | 'CAUTIOUS' | 'AGGRESSIVE' | 'LOCKED'
export type TopologyType = 'SEQUENTIAL' | 'PARALLEL' | 'PIPELINE' | 'MAP_REDUCE' | 'HIERARCHICAL'
export type DriftLevel = 'NONE' | 'LOW' | 'MODERATE' | 'HIGH' | 'CRITICAL'
export type Performative = 'REQUEST' | 'INFORM' | 'PROPOSE' | 'QUERY' | 'CONFIRM' | 'REFUSE' | 'AGREE'
export type SemanticFrame = 'DATA_PROCESSING' | 'ANALYSIS' | 'OPTIMIZATION' | 'GENERATION' | 'COMMUNICATION' | 'MONITORING' | 'TRANSFORMATION' | 'VERIFICATION' | 'CUSTOM'

export interface ProofObligation {
  axiom_id: number
  axiom_name: string
  description: string
  passed: boolean
  evidence?: string
}

export interface SubTask {
  id: string
  description: string
  risk_level: RiskLevel
  status: TaskStatus
  speculation_tier?: SpeculationTier
  output?: string | null
  dependencies: string[]
  proof_obligations?: ProofObligation[]
  parent_intent_id?: string | null
  required_role?: AgentRole | null
}

export interface Trace {
  id: string
  timestamp: string
  intent_id?: string
  task_id?: string
  event_type: string
  description: string
  details?: Record<string, unknown>
  risk_level: RiskLevel | null
  l0_passed: boolean | null
}

export interface RoutingDecision {
  task_id: string
  action: RoutingAction
  risk_level: RiskLevel
  speculation_tier: SpeculationTier
  reason: string
}

export interface ExecutionResult {
  intent_id: string
  output: string
  success: boolean
  sub_tasks: SubTask[]
  traces: Trace[]
  graph_summary: Record<string, unknown>
  rejected_tasks: SubTask[]
  exploration?: ExplorationResult | null
}

export interface WatchdogAlert {
  id?: string
  timestamp?: string
  severity: ContainmentLevel
  reason: string
  task_id?: string
  intent_id?: string
  rule?: string
}

export interface ApprovalRequest {
  intent_id: string
  task_id: string
  description: string
  risk_level: RiskLevel
  speculation_tier: SpeculationTier
  proof_obligations?: ProofObligation[]
  reason?: string
  status?: ApprovalStatus
  timestamp?: string
}

export interface AgentInfo {
  name: string
  role: AgentRole
  capabilities?: string[]
}

export interface DecompositionCandidate {
  id?: string
  subtasks?: SubTask[]
  score?: number
  critic_pass_rate?: number
  visit_count?: number
  parent_id?: string | null
  prompt_variant?: string
  temperature?: number
}

export interface MCTSNode {
  id?: string
  candidate?: DecompositionCandidate
  children?: string[]
  parent_id?: string | null
  visits?: number
  total_reward?: number
  ucb1_score?: number
}

export interface BeamState {
  id?: string
  decomposition_id?: string
  completed_tasks?: Record<string, string>
  score?: number
  wave_index?: number
  active?: boolean
}

export interface ConfidenceEstimate {
  task_id: string
  confidence?: number
  reasoning?: string
  calibrated?: boolean
}

export interface ExplorationResult {
  candidates_explored?: number
  best_decomposition_id?: string
  mcts_iterations?: number
  beam_width?: number
  beams_pruned?: number
  exploration_time_ms?: number
  confidence_estimates?: ConfidenceEstimate[]
}

export interface AutonomySettings {
  profile: AutonomyProfile
  override_matrix: Record<string, string>
  updated_at: string
}

export interface ReplayFrame {
  sequence: number
  trace_id?: string
  hash: string
  previous_hash?: string
  event_type: string
  description: string
  risk_level: RiskLevel | null
  l0_passed: boolean | null
  details?: Record<string, unknown>
  task_id?: string
  timestamp?: string
  counterfactual_action?: RoutingAction | null
}

export interface ReplaySession {
  intent_id: string
  total_frames: number
  frames: ReplayFrame[]
  chain_valid?: boolean
  chain_message?: string
}

export interface CounterfactualRequest {
  intent_id: string
  autonomy_settings: AutonomySettings
}

export interface CounterfactualResult {
  task_id: string
  task_description?: string
  actual_action: RoutingAction
  counterfactual_action: RoutingAction
  changed?: boolean
  risk_level?: RiskLevel
  speculation_tier?: SpeculationTier
}

export interface PrmStepScore {
  step_index: number
  description?: string
  score: number
  reasoning?: string
}

export interface PrmScore {
  task_id: string
  step_scores: PrmStepScore[]
  aggregate_score: number
  reasoning?: string
  timestamp?: string
}

export interface AgentDriftMetrics {
  agent_name: string
  total_executions: number
  recent_prm_scores?: number[]
  average_prm_score: number
  success_rate: number
  drift_level: DriftLevel
  last_updated?: string
}

export interface DelegationScope {
  allowed_risk_levels: RiskLevel[]
  allowed_actions?: RoutingAction[]
  allowed_capabilities?: string[]
  allowed_tool_categories?: string[]
  max_tasks: number
  max_depth?: number
  max_tool_calls?: number
}

export interface DelegationToken {
  id: string
  agent_id: string
  scope: DelegationScope
  issued_at: string
  expires_at: string
  parent_token_id: string | null
  signature?: string
  revoked: boolean
  tasks_executed: number
}

export interface TopologyRecommendation {
  topology?: TopologyType
  confidence?: number
  reasoning?: string
  graph_metrics?: Record<string, unknown>
}

export interface IntentV2 {
  id?: string
  created_at?: string
  performative?: Performative
  frame?: SemanticFrame
  description: string
  content_graph?: IntentNode[]
  root_node_id?: string | null
  constraints?: string[]
  context?: Record<string, unknown>
  language_game?: LanguageGameContext | null
  preconditions?: Precondition[]
  expected_effects?: ExpectedEffect[]
  risk_level?: RiskLevel | null
  speculation_tier?: SpeculationTier | null
  max_decomposition_depth?: number
  timeout_seconds?: number | null
  parent_intent_id?: string | null
  conversation_id?: string | null
}

export interface IntentNode {
  id?: string
  concept: string
  roles?: Record<string, string | string[]>
  properties?: Record<string, unknown>
}

export interface Precondition {
  expression: string
  verified?: boolean
  verification_method?: string
}

export interface ExpectedEffect {
  state: string
  confidence_threshold?: number
  verification_criteria?: string[]
}

export interface LanguageGameContext {
  game: string
  ontology?: string | null
  authority_level?: string
  cultural_context?: string | null
}

// ─── Pipeline & WebSocket types ──────────────────────────────

export interface PipelineStatus {
  running_pipelines: number
  completed_pipelines: number
  pending_approvals: number
  version: string
}

export interface WsMessage {
  type: 'trace' | 'approval_request' | 'autonomy_updated' | 'pipeline_complete' | 'pong' | 'error'
  intent_id?: string
  data?: Record<string, unknown>
  success?: boolean
  message?: string
}

// ─── SuperWork types ─────────────────────────────────────────

export type SessionStatus = 'INITIALIZING' | 'WATCHING' | 'PAUSED' | 'STOPPED'

export type ProposalStatus = 'PENDING' | 'APPROVED' | 'SKIPPED' | 'EXECUTING' | 'COMPLETED' | 'FAILED'

export interface TaskCompletionEvent {
  id: string
  session_id: string
  project_path: string
  completed_task: string
  output_summary: string
  files_changed: string[]
  errors: string[]
  duration_seconds: number
  timestamp: string
}

export interface TaskProposal {
  id: string
  title: string
  description: string
  rationale: string
  risk_level: RiskLevel
  estimated_tokens: number
  auto_execute: boolean
  dependencies: string[]
  status: ProposalStatus
  priority: number
  created_at: string
  resolved_at: string | null
}

export interface ProjectAnalysis {
  id: string
  total_tasks_completed: number
  total_tasks_failed: number
  velocity_tasks_per_hour: number
  focus_area: string
  summary: string
  proposals: TaskProposal[]
  status: string
  timestamp: string
}

export interface MetricsSnapshot {
  tasks_completed: number
  tasks_failed: number
  tokens_used: number
  cost_usd: number
  velocity_tasks_per_hour: number
  success_rate: number
  session_duration_seconds: number
  timestamp: string
}

export interface PredictionResult {
  remaining_tasks: number
  estimated_hours: number
  estimated_cost_usd: number
  estimated_completion: string | null
  confidence: number
}

export interface SuperWorkSession {
  id: string
  project_path: string
  status: SessionStatus
  started_at: string
  stopped_at: string | null
  metrics: MetricsSnapshot
  active_proposals: TaskProposal[]
}

export interface SuperWorkWsMessage {
  type: 'task_complete' | 'proposal_approved' | 'proposal_skipped' | 'pong'
  data?: TaskCompletionEvent
  proposal_id?: string
}
