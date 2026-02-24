"""
Kovrin Core Data Models

All shared types used across the framework. This module is the foundation
that every other component imports from — it must have zero internal
dependencies beyond pydantic.
"""

import uuid
from datetime import datetime, timezone
from enum import Enum

from pydantic import BaseModel, Field


# ─── Enums ───────────────────────────────────────────────────

class RiskLevel(str, Enum):
    """Risk classification for sub-tasks."""
    LOW = "LOW"
    MEDIUM = "MEDIUM"
    HIGH = "HIGH"
    CRITICAL = "CRITICAL"


class TaskStatus(str, Enum):
    """Lifecycle state of a sub-task."""
    PENDING = "PENDING"
    READY = "READY"
    EXECUTING = "EXECUTING"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"
    REJECTED_BY_L0 = "REJECTED_BY_L0"
    AWAITING_HUMAN = "AWAITING_HUMAN"
    SKIPPED = "SKIPPED"


class SpeculationTier(str, Enum):
    """Three-tier classification for parallel decision exploration.

    Based on the Speculative Actions paper (2025):
    - FREE: Read-only, idempotent -> parallel execution, no approval
    - GUARDED: Reversible -> sandbox with commit/rollback
    - NONE: Irreversible -> human confirmation required
    """
    FREE = "FREE"
    GUARDED = "GUARDED"
    NONE = "NONE"


class RoutingAction(str, Enum):
    """Decision from the risk router."""
    AUTO_EXECUTE = "AUTO_EXECUTE"
    SANDBOX_REVIEW = "SANDBOX_REVIEW"
    HUMAN_APPROVAL = "HUMAN_APPROVAL"


class ContainmentLevel(str, Enum):
    """Watchdog graduated containment response."""
    WARN = "WARN"
    PAUSE = "PAUSE"
    KILL = "KILL"


class AgentRole(str, Enum):
    """Specialized agent roles for multi-agent coordination."""
    RESEARCHER = "RESEARCHER"
    WRITER = "WRITER"
    REVIEWER = "REVIEWER"
    PLANNER = "PLANNER"
    SPECIALIST = "SPECIALIST"


class ToolCategory(str, Enum):
    """Classification of tool types for safety routing and DCT scope control."""
    READ_ONLY = "READ_ONLY"
    COMPUTATION = "COMPUTATION"
    NETWORK = "NETWORK"
    FILE_SYSTEM = "FILE_SYSTEM"
    CODE_EXECUTION = "CODE_EXECUTION"
    EXTERNAL_API = "EXTERNAL_API"


# ─── Proof Obligations ──────────────────────────────────────

class ProofObligation(BaseModel):
    """Result of checking a sub-task against a single Layer 0 axiom."""
    axiom_id: int
    axiom_name: str
    description: str
    passed: bool
    evidence: str = ""


# ─── Sub-Task ────────────────────────────────────────────────

class SubTask(BaseModel):
    """A decomposed unit of work derived from an intent."""
    id: str = Field(default_factory=lambda: f"task-{uuid.uuid4().hex[:8]}")
    description: str
    risk_level: RiskLevel = RiskLevel.LOW
    status: TaskStatus = TaskStatus.PENDING
    speculation_tier: SpeculationTier = SpeculationTier.FREE
    output: str | None = None
    dependencies: list[str] = Field(default_factory=list)
    proof_obligations: list[ProofObligation] = Field(default_factory=list)
    parent_intent_id: str | None = None
    required_role: AgentRole | None = None


# ─── Trace Event ─────────────────────────────────────────────

class Trace(BaseModel):
    """An immutable audit event in the execution pipeline."""
    id: str = Field(default_factory=lambda: f"tr-{uuid.uuid4().hex[:8]}")
    timestamp: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))
    intent_id: str = ""
    task_id: str = ""
    event_type: str = ""
    description: str = ""
    details: dict = Field(default_factory=dict)
    risk_level: RiskLevel | None = None
    l0_passed: bool | None = None


# ─── Routing Decision ───────────────────────────────────────

class RoutingDecision(BaseModel):
    """Output of the risk router for a single sub-task."""
    task_id: str
    action: RoutingAction
    risk_level: RiskLevel
    speculation_tier: SpeculationTier
    reason: str


# ─── Execution Result ───────────────────────────────────────

class ExecutionResult(BaseModel):
    """Final output of a Kovrin pipeline run."""
    intent_id: str
    output: str = ""
    success: bool = True
    sub_tasks: list[SubTask] = Field(default_factory=list)
    traces: list[Trace] = Field(default_factory=list)
    graph_summary: dict = Field(default_factory=dict)
    rejected_tasks: list[SubTask] = Field(default_factory=list)
    exploration: "ExplorationResult | None" = None


# ─── Watchdog ────────────────────────────────────────────────

class WatchdogAlert(BaseModel):
    """An alert raised by the watchdog agent."""
    id: str = Field(default_factory=lambda: f"alert-{uuid.uuid4().hex[:8]}")
    timestamp: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))
    severity: ContainmentLevel
    reason: str
    task_id: str = ""
    intent_id: str = ""
    rule: str = ""


# ─── Approval ───────────────────────────────────────────────

class ApprovalStatus(str, Enum):
    """Status of a human approval request."""
    PENDING = "PENDING"
    APPROVED = "APPROVED"
    REJECTED = "REJECTED"
    TIMEOUT = "TIMEOUT"


class ApprovalRequest(BaseModel):
    """A request for human approval of a high-risk task."""
    intent_id: str
    task_id: str
    description: str
    risk_level: RiskLevel
    speculation_tier: SpeculationTier
    proof_obligations: list[ProofObligation] = Field(default_factory=list)
    reason: str = ""
    status: ApprovalStatus = ApprovalStatus.PENDING
    timestamp: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))


# ─── Agent Info ──────────────────────────────────────────────

class AgentInfo(BaseModel):
    """Metadata about a specialized agent."""
    name: str
    role: AgentRole
    capabilities: list[str] = Field(default_factory=list)


# ─── Phase 4: Exploration Models ──────────────────────────────


class DecompositionCandidate(BaseModel):
    """A candidate decomposition generated during MCTS exploration."""
    id: str = Field(default_factory=lambda: f"dec-{uuid.uuid4().hex[:8]}")
    subtasks: list[SubTask] = Field(default_factory=list)
    score: float = 0.0
    critic_pass_rate: float = 0.0
    visit_count: int = 0
    parent_id: str | None = None
    prompt_variant: str = ""
    temperature: float = 1.0


class MCTSNode(BaseModel):
    """A node in the MCTS search tree over decompositions."""
    id: str = Field(default_factory=lambda: f"mcts-{uuid.uuid4().hex[:8]}")
    candidate: DecompositionCandidate = Field(default_factory=DecompositionCandidate)
    children: list[str] = Field(default_factory=list)
    parent_id: str | None = None
    visits: int = 0
    total_reward: float = 0.0
    ucb1_score: float = float("inf")


class BeamState(BaseModel):
    """State of a single beam during beam search execution."""
    id: str = Field(default_factory=lambda: f"beam-{uuid.uuid4().hex[:8]}")
    decomposition_id: str = ""
    completed_tasks: dict[str, str] = Field(default_factory=dict)
    score: float = 0.0
    wave_index: int = 0
    active: bool = True


class ConfidenceEstimate(BaseModel):
    """Claude-based confidence estimate for a task output."""
    task_id: str
    confidence: float = Field(0.5, ge=0.0, le=1.0)
    reasoning: str = ""
    calibrated: bool = False


class ExplorationResult(BaseModel):
    """Summary of the exploration process (MCTS + beam search)."""
    candidates_explored: int = 0
    best_decomposition_id: str = ""
    mcts_iterations: int = 0
    beam_width: int = 1
    beams_pruned: int = 0
    exploration_time_ms: float = 0.0
    confidence_estimates: list[ConfidenceEstimate] = Field(default_factory=list)


# ─── Phase 5: UX and Audit Models ───────────────────────────


class ViewMode(str, Enum):
    """Three-tier progressive disclosure for the dashboard."""
    OPERATOR = "OPERATOR"
    ANALYST = "ANALYST"
    DEVELOPER = "DEVELOPER"


class AutonomyProfile(str, Enum):
    """Named autonomy presets for risk routing overrides."""
    DEFAULT = "DEFAULT"
    CAUTIOUS = "CAUTIOUS"
    AGGRESSIVE = "AGGRESSIVE"
    LOCKED = "LOCKED"


class AutonomySettings(BaseModel):
    """Runtime autonomy configuration for the risk router.

    Applied after the default routing matrix. Cell overrides take
    precedence over profile overrides.
    """
    profile: AutonomyProfile = AutonomyProfile.DEFAULT
    override_matrix: dict[str, str] = Field(default_factory=dict)
    updated_at: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))


class ReplayFrame(BaseModel):
    """A single step in a decision replay session."""
    sequence: int = 0
    trace_id: str = ""
    hash: str = ""
    previous_hash: str = ""
    event_type: str = ""
    description: str = ""
    risk_level: RiskLevel | None = None
    l0_passed: bool | None = None
    details: dict = Field(default_factory=dict)
    task_id: str = ""
    timestamp: str = ""
    counterfactual_action: RoutingAction | None = None


class ReplaySession(BaseModel):
    """A loaded replay for a completed pipeline."""
    intent_id: str
    total_frames: int = 0
    frames: list[ReplayFrame] = Field(default_factory=list)
    chain_valid: bool = True
    chain_message: str = ""


class CounterfactualRequest(BaseModel):
    """What-if request: re-evaluate routing with alternate autonomy settings."""
    intent_id: str
    autonomy_settings: AutonomySettings


class CounterfactualResult(BaseModel):
    """Per-task routing diff between actual and hypothetical."""
    task_id: str
    task_description: str = ""
    actual_action: RoutingAction
    counterfactual_action: RoutingAction
    changed: bool = False
    risk_level: RiskLevel = RiskLevel.LOW
    speculation_tier: SpeculationTier = SpeculationTier.FREE


# ─── Phase 6: Advanced Alignment & Scaling Models ─────────


class TopologyType(str, Enum):
    """Execution topology for a task graph."""
    SEQUENTIAL = "SEQUENTIAL"
    PARALLEL = "PARALLEL"
    PIPELINE = "PIPELINE"
    MAP_REDUCE = "MAP_REDUCE"
    HIERARCHICAL = "HIERARCHICAL"


class PrmStepScore(BaseModel):
    """Score for a single reasoning step within a task output."""
    step_index: int
    description: str = ""
    score: float = Field(0.5, ge=0.0, le=1.0)
    reasoning: str = ""


class PrmScore(BaseModel):
    """Process Reward Model score for a complete task."""
    task_id: str
    step_scores: list[PrmStepScore] = Field(default_factory=list)
    aggregate_score: float = Field(0.5, ge=0.0, le=1.0)
    reasoning: str = ""
    timestamp: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))


class DriftLevel(str, Enum):
    """Severity of agent behavioral drift."""
    NONE = "NONE"
    LOW = "LOW"
    MODERATE = "MODERATE"
    HIGH = "HIGH"
    CRITICAL = "CRITICAL"


class AgentDriftMetrics(BaseModel):
    """Per-agent performance tracking for drift detection."""
    agent_name: str
    total_executions: int = 0
    recent_prm_scores: list[float] = Field(default_factory=list)
    average_prm_score: float = 0.0
    success_rate: float = 1.0
    drift_level: DriftLevel = DriftLevel.NONE
    last_updated: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))


class DelegationScope(BaseModel):
    """Defines the minimum-privilege boundary for a delegation token."""
    allowed_risk_levels: list[RiskLevel] = Field(default_factory=lambda: [RiskLevel.LOW])
    allowed_actions: list[RoutingAction] = Field(default_factory=lambda: [RoutingAction.AUTO_EXECUTE])
    allowed_capabilities: list[str] = Field(default_factory=list)
    allowed_tool_categories: list[ToolCategory] = Field(default_factory=list)
    max_tasks: int = 10
    max_depth: int = 1
    max_tool_calls: int = 50


class DelegationToken(BaseModel):
    """Cryptographically signed capability token for agent delegation."""
    id: str = Field(default_factory=lambda: f"dct-{uuid.uuid4().hex[:12]}")
    agent_id: str
    scope: DelegationScope = Field(default_factory=DelegationScope)
    issued_at: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))
    expires_at: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))
    parent_token_id: str | None = None
    signature: str = ""
    revoked: bool = False
    tasks_executed: int = 0


class TopologyRecommendation(BaseModel):
    """Result of automatic topology analysis."""
    topology: TopologyType = TopologyType.SEQUENTIAL
    confidence: float = Field(0.5, ge=0.0, le=1.0)
    reasoning: str = ""
    graph_metrics: dict = Field(default_factory=dict)
