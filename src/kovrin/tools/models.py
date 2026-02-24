"""
Kovrin Tool System Models

Pydantic models for the safety-gated tool execution system.
Every tool call is classified by risk, routed through the safety
pipeline, and logged to the Merkle audit trail.
"""

from __future__ import annotations

import uuid
from datetime import datetime, timezone
from enum import Enum
from typing import Any

from pydantic import BaseModel, Field

from kovrin.core.models import RiskLevel, RoutingAction, SpeculationTier


class ToolCategory(str, Enum):
    """Classification of tool types for safety routing and DCT scope control."""
    READ_ONLY = "READ_ONLY"
    COMPUTATION = "COMPUTATION"
    NETWORK = "NETWORK"
    FILE_SYSTEM = "FILE_SYSTEM"
    CODE_EXECUTION = "CODE_EXECUTION"
    EXTERNAL_API = "EXTERNAL_API"


class ToolRiskProfile(BaseModel):
    """Safety metadata attached to every registered tool.

    Determines how the SafeToolRouter classifies and routes
    calls to this tool through the safety pipeline.
    """
    risk_level: RiskLevel = RiskLevel.LOW
    speculation_tier: SpeculationTier = SpeculationTier.FREE
    category: ToolCategory = ToolCategory.READ_ONLY
    scope_tags: list[str] = Field(default_factory=list)
    max_calls_per_task: int = Field(default=10, ge=1, le=1000)
    requires_approval: bool = False


class ToolCallRequest(BaseModel):
    """A pending tool call from Claude that needs safety validation.

    Created when the LLM returns a tool_use response block.
    The SafeToolRouter evaluates this before execution.
    """
    id: str = Field(default_factory=lambda: f"tc-{uuid.uuid4().hex[:8]}")
    tool_name: str
    tool_input: dict[str, Any] = Field(default_factory=dict)
    tool_use_id: str = ""
    task_id: str = ""
    intent_id: str = ""
    agent_id: str | None = None


class ToolCallDecision(BaseModel):
    """Result of safety evaluation for a single tool call.

    Produced by SafeToolRouter.evaluate(). If allowed=False,
    the tool call is blocked and the reason is fed back to Claude.
    """
    allowed: bool
    action: RoutingAction
    reason: str
    risk_level: RiskLevel = RiskLevel.LOW
    speculation_tier: SpeculationTier = SpeculationTier.FREE
    requires_approval: bool = False
    tool_name: str = ""


class ToolCallTrace(BaseModel):
    """Audit record for a tool execution, logged to the Merkle chain.

    Contains both the request and the safety decision so the
    complete tool call lifecycle is auditable.
    """
    id: str = Field(default_factory=lambda: f"tct-{uuid.uuid4().hex[:8]}")
    timestamp: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))
    tool_name: str = ""
    tool_input: dict[str, Any] = Field(default_factory=dict)
    tool_output: str = ""
    risk_level: RiskLevel = RiskLevel.LOW
    routing_action: RoutingAction = RoutingAction.AUTO_EXECUTE
    execution_time_ms: float = 0.0
    sandboxed: bool = False
    blocked: bool = False
    block_reason: str = ""
    task_id: str = ""
    intent_id: str = ""
    agent_id: str | None = None
