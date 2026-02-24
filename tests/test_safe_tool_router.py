"""Tests for the Kovrin SafeToolRouter.

Covers safety evaluation, routing decisions, rate limiting,
and integration with RiskRouter.
"""

import pytest

from kovrin.agents.tools import ToolDefinition
from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import RiskLevel, RoutingAction, SpeculationTier
from kovrin.engine.risk_router import RiskRouter
from kovrin.tools.models import ToolCallRequest, ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool, ToolRegistry
from kovrin.tools.router import SafeToolRouter


def _make_registry() -> ToolRegistry:
    """Create a registry with test tools at different risk levels."""
    registry = ToolRegistry()

    registry.register(RegisteredTool(
        definition=ToolDefinition(
            name="safe_calc",
            description="Calculator",
            input_schema={"type": "object", "properties": {"expr": {"type": "string"}}, "required": ["expr"]},
        ),
        risk_profile=ToolRiskProfile(
            risk_level=RiskLevel.LOW,
            speculation_tier=SpeculationTier.FREE,
            category=ToolCategory.COMPUTATION,
            scope_tags=["computation"],
            max_calls_per_task=5,
        ),
        handler=lambda expr: str(eval(expr, {"__builtins__": {}})),  # noqa: S307
    ))

    registry.register(RegisteredTool(
        definition=ToolDefinition(
            name="risky_network",
            description="HTTP request",
            input_schema={"type": "object", "properties": {"url": {"type": "string"}}, "required": ["url"]},
        ),
        risk_profile=ToolRiskProfile(
            risk_level=RiskLevel.MEDIUM,
            speculation_tier=SpeculationTier.GUARDED,
            category=ToolCategory.NETWORK,
            scope_tags=["network"],
        ),
        handler=lambda url: f"Fetched {url}",
    ))

    registry.register(RegisteredTool(
        definition=ToolDefinition(
            name="danger_code",
            description="Code execution",
            input_schema={"type": "object", "properties": {"code": {"type": "string"}}, "required": ["code"]},
        ),
        risk_profile=ToolRiskProfile(
            risk_level=RiskLevel.HIGH,
            speculation_tier=SpeculationTier.GUARDED,
            category=ToolCategory.CODE_EXECUTION,
            scope_tags=["code_execution"],
        ),
        handler=lambda code: "executed",
    ))

    registry.register(RegisteredTool(
        definition=ToolDefinition(
            name="critical_action",
            description="Critical action",
            input_schema={"type": "object", "properties": {}},
        ),
        risk_profile=ToolRiskProfile(
            risk_level=RiskLevel.CRITICAL,
            speculation_tier=SpeculationTier.NONE,
            category=ToolCategory.EXTERNAL_API,
            scope_tags=["critical"],
        ),
        handler=lambda: "done",
    ))

    return registry


def _make_router(registry: ToolRegistry | None = None, trace_log: ImmutableTraceLog | None = None) -> SafeToolRouter:
    return SafeToolRouter(
        registry=registry or _make_registry(),
        risk_router=RiskRouter(),
        trace_log=trace_log,
    )


class TestSafetyRouting:
    """Tests for safety evaluation of tool calls."""

    @pytest.mark.asyncio
    async def test_low_risk_tool_auto_executes(self):
        router = _make_router()
        request = ToolCallRequest(
            tool_name="safe_calc",
            tool_input={"expr": "2+2"},
            tool_use_id="tu-1",
            task_id="t1",
            intent_id="i1",
        )
        decision = await router.evaluate(request)
        assert decision.allowed is True
        assert decision.action == RoutingAction.AUTO_EXECUTE

    @pytest.mark.asyncio
    async def test_medium_risk_tool_sandbox_review(self):
        router = _make_router()
        request = ToolCallRequest(
            tool_name="risky_network",
            tool_input={"url": "https://example.com"},
            tool_use_id="tu-2",
            task_id="t1",
            intent_id="i1",
        )
        decision = await router.evaluate(request)
        assert decision.allowed is True
        # MEDIUM + GUARDED → SANDBOX_REVIEW
        assert decision.action == RoutingAction.SANDBOX_REVIEW

    @pytest.mark.asyncio
    async def test_high_risk_tool_requires_approval(self):
        """HIGH + GUARDED → HUMAN_APPROVAL, but no callback → blocked."""
        router = _make_router()
        request = ToolCallRequest(
            tool_name="danger_code",
            tool_input={"code": "print(1)"},
            tool_use_id="tu-3",
            task_id="t1",
            intent_id="i1",
        )
        decision = await router.evaluate(request)
        # HIGH + GUARDED → HUMAN_APPROVAL, no callback → not allowed
        assert decision.allowed is False
        assert decision.action == RoutingAction.HUMAN_APPROVAL

    @pytest.mark.asyncio
    async def test_critical_tool_always_requires_approval(self):
        """CRITICAL risk → HUMAN_APPROVAL regardless of any override."""
        router = _make_router()
        request = ToolCallRequest(
            tool_name="critical_action",
            tool_input={},
            tool_use_id="tu-4",
            task_id="t1",
            intent_id="i1",
        )
        decision = await router.evaluate(request)
        assert decision.action == RoutingAction.HUMAN_APPROVAL
        assert decision.allowed is False  # No approval callback

    @pytest.mark.asyncio
    async def test_unknown_tool_blocked(self):
        router = _make_router()
        request = ToolCallRequest(
            tool_name="nonexistent_tool",
            tool_input={},
            tool_use_id="tu-5",
            task_id="t1",
            intent_id="i1",
        )
        decision = await router.evaluate(request)
        assert decision.allowed is False
        assert "Unknown tool" in decision.reason


class TestRateLimiting:
    """Tests for per-task tool call rate limiting."""

    @pytest.mark.asyncio
    async def test_rate_limit_blocks_after_max_calls(self):
        router = _make_router()

        for i in range(5):
            request = ToolCallRequest(
                tool_name="safe_calc",
                tool_input={"expr": f"{i}+1"},
                tool_use_id=f"tu-{i}",
                task_id="t1",
                intent_id="i1",
            )
            decision = await router.evaluate(request)
            assert decision.allowed is True, f"Call {i} should be allowed"

        # 6th call should be blocked (max_calls_per_task=5)
        request = ToolCallRequest(
            tool_name="safe_calc",
            tool_input={"expr": "6+1"},
            tool_use_id="tu-6",
            task_id="t1",
            intent_id="i1",
        )
        decision = await router.evaluate(request)
        assert decision.allowed is False
        assert "Rate limit" in decision.reason

    @pytest.mark.asyncio
    async def test_rate_limit_per_task_isolation(self):
        """Rate limits are tracked per task — different tasks don't interfere."""
        router = _make_router()

        # 5 calls from task t1
        for i in range(5):
            await router.evaluate(ToolCallRequest(
                tool_name="safe_calc",
                tool_input={"expr": f"{i}"},
                tool_use_id=f"tu-t1-{i}",
                task_id="t1",
                intent_id="i1",
            ))

        # First call from task t2 should still be allowed
        decision = await router.evaluate(ToolCallRequest(
            tool_name="safe_calc",
            tool_input={"expr": "1"},
            tool_use_id="tu-t2-1",
            task_id="t2",
            intent_id="i1",
        ))
        assert decision.allowed is True

    @pytest.mark.asyncio
    async def test_reset_counts(self):
        router = _make_router()

        for i in range(5):
            await router.evaluate(ToolCallRequest(
                tool_name="safe_calc",
                tool_input={"expr": f"{i}"},
                tool_use_id=f"tu-{i}",
                task_id="t1",
                intent_id="i1",
            ))

        router.reset_counts("t1")

        decision = await router.evaluate(ToolCallRequest(
            tool_name="safe_calc",
            tool_input={"expr": "1"},
            tool_use_id="tu-after-reset",
            task_id="t1",
            intent_id="i1",
        ))
        assert decision.allowed is True


class TestToolExecution:
    """Tests for tool execution through the router."""

    @pytest.mark.asyncio
    async def test_execute_allowed_tool(self):
        router = _make_router()
        request = ToolCallRequest(
            tool_name="safe_calc",
            tool_input={"expr": "2+2"},
            tool_use_id="tu-1",
            task_id="t1",
            intent_id="i1",
        )
        decision = await router.evaluate(request)
        result = await router.execute_if_allowed(request, decision)
        assert result.content == "4"
        assert result.is_error is False

    @pytest.mark.asyncio
    async def test_execute_blocked_tool_returns_error(self):
        from kovrin.tools.models import ToolCallDecision
        router = _make_router()
        request = ToolCallRequest(
            tool_name="safe_calc",
            tool_input={"expr": "2+2"},
            tool_use_id="tu-1",
            task_id="t1",
            intent_id="i1",
        )
        blocked_decision = ToolCallDecision(
            allowed=False,
            action=RoutingAction.HUMAN_APPROVAL,
            reason="Blocked for test",
            tool_name="safe_calc",
        )
        result = await router.execute_if_allowed(request, blocked_decision)
        assert result.is_error is True
        assert "BLOCKED BY SAFETY" in result.content

    @pytest.mark.asyncio
    async def test_execute_nonexistent_tool(self):
        from kovrin.tools.models import ToolCallDecision
        router = _make_router()
        request = ToolCallRequest(
            tool_name="ghost_tool",
            tool_input={},
            tool_use_id="tu-1",
            task_id="t1",
            intent_id="i1",
        )
        decision = ToolCallDecision(
            allowed=True,
            action=RoutingAction.AUTO_EXECUTE,
            reason="test",
            tool_name="ghost_tool",
        )
        result = await router.execute_if_allowed(request, decision)
        assert result.is_error is True
        assert "not found" in result.content


class TestAuditTrail:
    """Tests for Merkle audit trail integration."""

    @pytest.mark.asyncio
    async def test_allowed_call_logged_to_trace(self):
        trace_log = ImmutableTraceLog()
        router = _make_router(trace_log=trace_log)

        request = ToolCallRequest(
            tool_name="safe_calc",
            tool_input={"expr": "1+1"},
            tool_use_id="tu-1",
            task_id="t1",
            intent_id="i1",
        )
        decision = await router.evaluate(request)
        await router.execute_if_allowed(request, decision)

        # Should have at least 2 events: evaluation + execution
        events = trace_log.get_events()
        assert len(events) >= 2
        event_types = [e.trace.event_type for e in events]
        assert "TOOL_CALL_EVALUATED" in event_types
        assert "TOOL_CALL_EXECUTED" in event_types

    @pytest.mark.asyncio
    async def test_blocked_call_logged_to_trace(self):
        trace_log = ImmutableTraceLog()
        router = _make_router(trace_log=trace_log)

        request = ToolCallRequest(
            tool_name="nonexistent",
            tool_input={},
            tool_use_id="tu-1",
            task_id="t1",
            intent_id="i1",
        )
        await router.evaluate(request)

        events = trace_log.get_events()
        assert len(events) >= 1
        assert events[0].trace.event_type == "TOOL_CALL_BLOCKED"

    @pytest.mark.asyncio
    async def test_merkle_chain_intact_after_tool_calls(self):
        trace_log = ImmutableTraceLog()
        router = _make_router(trace_log=trace_log)

        for i in range(3):
            request = ToolCallRequest(
                tool_name="safe_calc",
                tool_input={"expr": f"{i}+1"},
                tool_use_id=f"tu-{i}",
                task_id="t1",
                intent_id="i1",
            )
            decision = await router.evaluate(request)
            await router.execute_if_allowed(request, decision)

        valid, msg = trace_log.verify_integrity()
        assert valid is True, f"Merkle chain broken: {msg}"
