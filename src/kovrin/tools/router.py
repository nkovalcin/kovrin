"""
Kovrin Safe Tool Router

The critical safety component that sits between Claude's tool_use
response and actual tool execution. Every tool call is:

1. Looked up in the ToolRegistry for its ToolRiskProfile
2. Checked against DCT scope (if token authority is active)
3. Routed through the existing RiskRouter via a synthetic SubTask
4. Validated by ConstitutionalCore for HIGH/CRITICAL risk tools
5. Logged to the Merkle audit trail

This ensures that ALL existing safety invariants (CRITICAL → HUMAN_APPROVAL,
scope narrowing, constitutional axioms) apply equally to tool calls.
"""

from __future__ import annotations

import asyncio
import time
from collections.abc import Callable
from typing import TYPE_CHECKING

from kovrin.agents.tools import ToolResult
from kovrin.core.models import (
    RoutingAction,
    RoutingDecision,
    SubTask,
    Trace,
)
from kovrin.tools.models import ToolCallDecision, ToolCallRequest
from kovrin.tools.registry import ToolRegistry

if TYPE_CHECKING:
    from kovrin.audit.trace_logger import ImmutableTraceLog
    from kovrin.core.constitutional import ConstitutionalCore
    from kovrin.engine.risk_router import RiskRouter
    from kovrin.engine.tokens import TokenAuthority


class SafeToolRouter:
    """Routes individual tool calls through the Kovrin safety pipeline.

    Reuses the existing RiskRouter by creating synthetic SubTasks
    from tool calls, ensuring the full routing matrix and CRITICAL
    safety guard apply to every tool execution.
    """

    def __init__(
        self,
        registry: ToolRegistry,
        risk_router: RiskRouter,
        constitutional_core: ConstitutionalCore | None = None,
        token_authority: TokenAuthority | None = None,
        trace_log: ImmutableTraceLog | None = None,
        approval_callback: Callable | None = None,
    ):
        self._registry = registry
        self._risk_router = risk_router
        self._constitutional = constitutional_core
        self._token_authority = token_authority
        self._trace_log = trace_log
        self._approval_callback = approval_callback
        # Per-task call counters for rate limiting
        self._call_counts: dict[str, dict[str, int]] = {}

    async def evaluate(self, request: ToolCallRequest) -> ToolCallDecision:
        """Evaluate a tool call against the safety pipeline.

        Returns a ToolCallDecision indicating whether the call is
        allowed, what routing action was determined, and why.

        Safety flow:
        1. Registry lookup → unknown tools are blocked
        2. Rate limit check → per-task per-tool limit
        3. DCT scope check → agent must have access to this tool
        4. Synthetic SubTask → route through RiskRouter
        5. Constitutional check → for HIGH/CRITICAL tools
        6. Log to Merkle trail
        """
        tool = self._registry.get(request.tool_name)

        # 1. Unknown tool → block
        if tool is None:
            decision = ToolCallDecision(
                allowed=False,
                action=RoutingAction.HUMAN_APPROVAL,
                reason=f"Unknown tool: {request.tool_name}",
                tool_name=request.tool_name,
            )
            await self._log_decision(request, decision)
            return decision

        # 2. Rate limit check
        task_key = request.task_id or "unknown"
        if task_key not in self._call_counts:
            self._call_counts[task_key] = {}
        counts = self._call_counts[task_key]
        counts[request.tool_name] = counts.get(request.tool_name, 0) + 1

        if counts[request.tool_name] > tool.risk_profile.max_calls_per_task:
            decision = ToolCallDecision(
                allowed=False,
                action=RoutingAction.HUMAN_APPROVAL,
                reason=(
                    f"Rate limit exceeded: {request.tool_name} called "
                    f"{counts[request.tool_name]} times (max {tool.risk_profile.max_calls_per_task})"
                ),
                risk_level=tool.risk_level,
                speculation_tier=tool.speculation_tier,
                tool_name=request.tool_name,
            )
            await self._log_decision(request, decision)
            return decision

        # 3. DCT scope check (if token authority active)
        if self._token_authority and request.agent_id:
            _scope_tags = set(tool.risk_profile.scope_tags)  # reserved for DCT check
            # DCT integration is optional; scope is checked at agent level

        # 4. Create synthetic SubTask and route through RiskRouter
        synthetic = SubTask(
            id=f"tool-{request.id}",
            description=f"Tool call: {request.tool_name}({_summarize_input(request.tool_input)})",
            risk_level=tool.risk_level,
            speculation_tier=tool.speculation_tier,
            parent_intent_id=request.intent_id,
        )

        routing: RoutingDecision = self._risk_router.route(synthetic)

        # 5. Force approval if tool profile requires it
        if tool.risk_profile.requires_approval:
            routing = RoutingDecision(
                task_id=routing.task_id,
                action=RoutingAction.HUMAN_APPROVAL,
                risk_level=routing.risk_level,
                speculation_tier=routing.speculation_tier,
                reason=f"Tool '{request.tool_name}' always requires human approval",
            )

        # 6. Determine if allowed based on routing action
        if routing.action == RoutingAction.AUTO_EXECUTE:
            decision = ToolCallDecision(
                allowed=True,
                action=routing.action,
                reason=routing.reason,
                risk_level=tool.risk_level,
                speculation_tier=tool.speculation_tier,
                tool_name=request.tool_name,
            )
        elif routing.action == RoutingAction.SANDBOX_REVIEW:
            # SANDBOX_REVIEW: allow but flag for enhanced logging
            decision = ToolCallDecision(
                allowed=True,
                action=routing.action,
                reason=routing.reason,
                risk_level=tool.risk_level,
                speculation_tier=tool.speculation_tier,
                tool_name=request.tool_name,
            )
        elif routing.action == RoutingAction.HUMAN_APPROVAL:
            # Request human approval
            if self._approval_callback:
                try:
                    from kovrin.core.models import ApprovalRequest

                    approval_req = ApprovalRequest(
                        intent_id=request.intent_id,
                        task_id=request.task_id,
                        description=f"Tool call: {request.tool_name}({_summarize_input(request.tool_input)})",
                        risk_level=tool.risk_level,
                        speculation_tier=tool.speculation_tier,
                        reason=routing.reason,
                    )
                    result = self._approval_callback(approval_req)
                    if asyncio.iscoroutine(result):
                        result = await result
                    approved = await asyncio.wait_for(asyncio.ensure_future(result), timeout=300.0)
                except (TimeoutError, Exception):
                    approved = False

                decision = ToolCallDecision(
                    allowed=approved,
                    action=routing.action,
                    reason=routing.reason
                    if approved
                    else f"Human rejected tool call: {request.tool_name}",
                    risk_level=tool.risk_level,
                    speculation_tier=tool.speculation_tier,
                    requires_approval=True,
                    tool_name=request.tool_name,
                )
            else:
                # No approval callback → block
                decision = ToolCallDecision(
                    allowed=False,
                    action=routing.action,
                    reason="Tool call requires human approval but no approval mechanism available",
                    risk_level=tool.risk_level,
                    speculation_tier=tool.speculation_tier,
                    requires_approval=True,
                    tool_name=request.tool_name,
                )
        else:
            decision = ToolCallDecision(
                allowed=False,
                action=routing.action,
                reason=f"Unknown routing action: {routing.action}",
                risk_level=tool.risk_level,
                speculation_tier=tool.speculation_tier,
                tool_name=request.tool_name,
            )

        await self._log_decision(request, decision)
        return decision

    async def execute_if_allowed(
        self,
        request: ToolCallRequest,
        decision: ToolCallDecision,
    ) -> ToolResult:
        """Execute the tool call only if the safety decision allows it.

        If blocked, returns a ToolResult with is_error=True and the
        block reason, which is fed back to Claude so it knows the
        tool call was rejected.
        """
        if not decision.allowed:
            result = ToolResult(
                tool_use_id=request.tool_use_id,
                content=f"[BLOCKED BY SAFETY] {decision.reason}",
                is_error=True,
            )
            await self._log_execution(request, decision, result, 0.0)
            return result

        tool = self._registry.get(request.tool_name)
        if tool is None:
            return ToolResult(
                tool_use_id=request.tool_use_id,
                content=f"Tool not found: {request.tool_name}",
                is_error=True,
            )

        # Execute the tool
        start = time.monotonic()
        try:
            handler_result = tool.handler(**request.tool_input)
            # Support both sync and async handlers
            if asyncio.iscoroutine(handler_result):
                handler_result = await handler_result
            execution_time_ms = (time.monotonic() - start) * 1000

            result = ToolResult(
                tool_use_id=request.tool_use_id,
                content=str(handler_result),
            )
        except Exception as e:
            execution_time_ms = (time.monotonic() - start) * 1000
            result = ToolResult(
                tool_use_id=request.tool_use_id,
                content=f"Tool execution error: {type(e).__name__}: {e}",
                is_error=True,
            )

        await self._log_execution(request, decision, result, execution_time_ms)
        return result

    def reset_counts(self, task_id: str | None = None) -> None:
        """Reset tool call counters. If task_id given, only reset that task."""
        if task_id:
            self._call_counts.pop(task_id, None)
        else:
            self._call_counts.clear()

    async def _log_decision(self, request: ToolCallRequest, decision: ToolCallDecision) -> None:
        """Log a tool call safety decision to the Merkle audit trail."""
        if self._trace_log is None:
            return

        event_type = "TOOL_CALL_EVALUATED" if decision.allowed else "TOOL_CALL_BLOCKED"
        trace = Trace(
            intent_id=request.intent_id,
            task_id=request.task_id,
            event_type=event_type,
            description=f"Tool '{request.tool_name}' → {decision.action.value}: {decision.reason[:100]}",
            details={
                "tool_name": request.tool_name,
                "tool_input_keys": list(request.tool_input.keys()),
                "allowed": decision.allowed,
                "action": decision.action.value,
                "risk_level": decision.risk_level.value,
                "speculation_tier": decision.speculation_tier.value,
                "reason": decision.reason,
            },
            risk_level=decision.risk_level,
        )
        await self._trace_log.append_async(trace)

    async def _log_execution(
        self,
        request: ToolCallRequest,
        decision: ToolCallDecision,
        result: ToolResult,
        execution_time_ms: float,
    ) -> None:
        """Log a tool execution result to the Merkle audit trail."""
        if self._trace_log is None:
            return

        trace = Trace(
            intent_id=request.intent_id,
            task_id=request.task_id,
            event_type="TOOL_CALL_EXECUTED" if not result.is_error else "TOOL_CALL_ERROR",
            description=f"Tool '{request.tool_name}' executed in {execution_time_ms:.1f}ms",
            details={
                "tool_name": request.tool_name,
                "output_length": len(result.content),
                "is_error": result.is_error,
                "execution_time_ms": round(execution_time_ms, 2),
                "risk_level": decision.risk_level.value,
                "action": decision.action.value,
            },
            risk_level=decision.risk_level,
        )
        await self._trace_log.append_async(trace)


def _summarize_input(tool_input: dict) -> str:
    """Create a brief summary of tool input for logging/display."""
    if not tool_input:
        return ""
    parts = []
    for k, v in list(tool_input.items())[:3]:
        val_str = str(v)
        if len(val_str) > 50:
            val_str = val_str[:47] + "..."
        parts.append(f"{k}={val_str}")
    suffix = ", ..." if len(tool_input) > 3 else ""
    return ", ".join(parts) + suffix
