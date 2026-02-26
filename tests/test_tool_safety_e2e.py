"""End-to-end tests for tool execution safety gates.

Tests the full SafeToolRouter flow: tool registry → risk routing →
rate limiting → approval gates → Merkle audit logging.
"""

import pytest

from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.constitutional import ConstitutionalCore
from kovrin.core.models import RiskLevel, RoutingAction, SpeculationTier
from kovrin.engine.risk_router import RiskRouter
from kovrin.tools.models import ToolCallRequest, ToolRiskProfile
from kovrin.tools.registry import ToolRegistry
from kovrin.tools.router import SafeToolRouter


def _setup_router(
    trace_log: ImmutableTraceLog | None = None,
    approval_callback=None,
) -> tuple[SafeToolRouter, ToolRegistry]:
    """Create a SafeToolRouter with built-in tools registered."""
    from kovrin.tools.builtin import register_all_builtins

    registry = ToolRegistry()
    register_all_builtins(registry)
    router = SafeToolRouter(
        registry=registry,
        risk_router=RiskRouter(),
        trace_log=trace_log,
        approval_callback=approval_callback,
    )
    return router, registry


# ─── Tool Discovery & Routing ────────────────────────────────


class TestToolDiscoveryAndRouting:
    """Verify tools are found, risk-classified, and routed correctly."""

    @pytest.mark.asyncio
    async def test_calculator_auto_executes(self):
        """Calculator is LOW/FREE → AUTO_EXECUTE."""
        router, _ = _setup_router()
        request = ToolCallRequest(
            tool_name="calculator",
            tool_input={"expression": "2 + 2"},
            task_id="t-1",
            intent_id="i-1",
        )
        decision = await router.evaluate(request)
        assert decision.allowed is True
        assert decision.action == RoutingAction.AUTO_EXECUTE

    @pytest.mark.asyncio
    async def test_web_search_auto_executes(self):
        """Web search is LOW/FREE → AUTO_EXECUTE."""
        router, _ = _setup_router()
        request = ToolCallRequest(
            tool_name="web_search",
            tool_input={"query": "AI safety"},
            task_id="t-1",
            intent_id="i-1",
        )
        decision = await router.evaluate(request)
        assert decision.allowed is True

    @pytest.mark.asyncio
    async def test_unknown_tool_blocked(self):
        """Unknown tools are always blocked."""
        router, _ = _setup_router()
        request = ToolCallRequest(
            tool_name="nonexistent_tool",
            tool_input={},
            task_id="t-1",
            intent_id="i-1",
        )
        decision = await router.evaluate(request)
        assert decision.allowed is False
        assert "Unknown tool" in decision.reason

    @pytest.mark.asyncio
    async def test_file_write_requires_review(self):
        """File write is MEDIUM/GUARDED → SANDBOX_REVIEW."""
        router, registry = _setup_router()

        # Verify file_write is registered
        tool = registry.get("file_write")
        assert tool is not None

        request = ToolCallRequest(
            tool_name="file_write",
            tool_input={"path": "/tmp/test.txt", "content": "hello"},
            task_id="t-1",
            intent_id="i-1",
        )
        decision = await router.evaluate(request)
        # MEDIUM/GUARDED → SANDBOX_REVIEW (allowed with logging)
        assert decision.allowed is True
        assert decision.action == RoutingAction.SANDBOX_REVIEW


# ─── Rate Limiting ───────────────────────────────────────────


class TestRateLimiting:
    """Per-task per-tool rate limits."""

    @pytest.mark.asyncio
    async def test_rate_limit_blocks_after_max(self):
        """Exceeding max_calls_per_task blocks the tool."""
        router, registry = _setup_router()

        # Find the calculator's max calls
        tool = registry.get("calculator")
        max_calls = tool.risk_profile.max_calls_per_task

        request = ToolCallRequest(
            tool_name="calculator",
            tool_input={"expression": "1+1"},
            task_id="t-rate",
            intent_id="i-1",
        )

        # Call up to limit
        for _ in range(max_calls):
            decision = await router.evaluate(request)
            assert decision.allowed is True

        # Next call should be blocked
        decision = await router.evaluate(request)
        assert decision.allowed is False
        assert "Rate limit" in decision.reason

    @pytest.mark.asyncio
    async def test_rate_limit_is_per_task(self):
        """Rate limits are per-task, not global."""
        router, _ = _setup_router()

        req1 = ToolCallRequest(
            tool_name="calculator",
            tool_input={"expression": "1"},
            task_id="t-1",
            intent_id="i-1",
        )
        req2 = ToolCallRequest(
            tool_name="calculator",
            tool_input={"expression": "2"},
            task_id="t-2",
            intent_id="i-1",
        )

        # Both should work independently
        d1 = await router.evaluate(req1)
        d2 = await router.evaluate(req2)
        assert d1.allowed is True
        assert d2.allowed is True

    @pytest.mark.asyncio
    async def test_reset_counts(self):
        """reset_counts clears rate limiting for a task."""
        router, registry = _setup_router()
        tool = registry.get("calculator")
        max_calls = tool.risk_profile.max_calls_per_task

        request = ToolCallRequest(
            tool_name="calculator",
            tool_input={"expression": "1"},
            task_id="t-reset",
            intent_id="i-1",
        )

        # Exhaust limit
        for _ in range(max_calls):
            await router.evaluate(request)

        decision = await router.evaluate(request)
        assert decision.allowed is False

        # Reset and try again
        router.reset_counts("t-reset")
        decision = await router.evaluate(request)
        assert decision.allowed is True


# ─── Merkle Audit Logging ────────────────────────────────────


class TestToolAuditLogging:
    """Tool calls are logged to the Merkle audit trail."""

    @pytest.mark.asyncio
    async def test_allowed_call_logged(self):
        """Allowed tool calls are logged as TOOL_CALL_EVALUATED."""
        trace_log = ImmutableTraceLog()
        router, _ = _setup_router(trace_log=trace_log)

        request = ToolCallRequest(
            tool_name="calculator",
            tool_input={"expression": "2+2"},
            task_id="t-1",
            intent_id="i-1",
        )
        await router.evaluate(request)

        events = trace_log.get_events()
        assert len(events) == 1
        assert events[0].trace.event_type == "TOOL_CALL_EVALUATED"
        assert events[0].trace.details["tool_name"] == "calculator"
        assert events[0].trace.details["allowed"] is True

    @pytest.mark.asyncio
    async def test_blocked_call_logged(self):
        """Blocked tool calls are logged as TOOL_CALL_BLOCKED."""
        trace_log = ImmutableTraceLog()
        router, _ = _setup_router(trace_log=trace_log)

        request = ToolCallRequest(
            tool_name="unknown_tool",
            tool_input={},
            task_id="t-1",
            intent_id="i-1",
        )
        await router.evaluate(request)

        events = trace_log.get_events()
        assert len(events) == 1
        assert events[0].trace.event_type == "TOOL_CALL_BLOCKED"
        assert events[0].trace.details["allowed"] is False

    @pytest.mark.asyncio
    async def test_audit_chain_integrity_after_tool_calls(self):
        """Merkle chain remains valid after multiple tool call events."""
        trace_log = ImmutableTraceLog()
        router, _ = _setup_router(trace_log=trace_log)

        # Mix of allowed and blocked calls
        for i in range(5):
            request = ToolCallRequest(
                tool_name="calculator" if i % 2 == 0 else "unknown",
                tool_input={"expression": str(i)} if i % 2 == 0 else {},
                task_id=f"t-{i}",
                intent_id="i-1",
            )
            await router.evaluate(request)

        valid, _ = trace_log.verify_integrity()
        assert valid is True
        assert len(trace_log.get_events()) == 5


# ─── Tool Execution ─────────────────────────────────────────


class TestToolExecution:
    """Test execute_if_allowed for allowed and blocked calls."""

    @pytest.mark.asyncio
    async def test_execute_allowed_call(self):
        """Allowed call executes the tool and returns result."""
        router, _ = _setup_router()

        request = ToolCallRequest(
            tool_name="calculator",
            tool_input={"expression": "3 * 7"},
            tool_use_id="tu-1",
            task_id="t-1",
            intent_id="i-1",
        )
        decision = await router.evaluate(request)
        assert decision.allowed is True

        result = await router.execute_if_allowed(request, decision)
        assert result.is_error is False
        assert "21" in result.content

    @pytest.mark.asyncio
    async def test_execute_blocked_call_returns_error(self):
        """Blocked call returns error result without executing."""
        router, _ = _setup_router()

        request = ToolCallRequest(
            tool_name="unknown_tool",
            tool_input={},
            tool_use_id="tu-2",
            task_id="t-1",
            intent_id="i-1",
        )
        decision = await router.evaluate(request)
        assert decision.allowed is False

        result = await router.execute_if_allowed(request, decision)
        assert result.is_error is True
        assert "BLOCKED BY SAFETY" in result.content

    @pytest.mark.asyncio
    async def test_execute_datetime_tool(self):
        """current_datetime tool returns current time."""
        router, _ = _setup_router()

        request = ToolCallRequest(
            tool_name="current_datetime",
            tool_input={},
            tool_use_id="tu-3",
            task_id="t-1",
            intent_id="i-1",
        )
        decision = await router.evaluate(request)
        result = await router.execute_if_allowed(request, decision)

        assert result.is_error is False
        assert "202" in result.content  # Should contain year


# ─── Builtin Tool Registry ──────────────────────────────────


class TestBuiltinToolRegistry:
    """Verify all 8 built-in tools are registered with correct risk profiles."""

    def test_all_builtins_registered(self):
        from kovrin.tools.builtin import register_all_builtins

        registry = ToolRegistry()
        register_all_builtins(registry)

        all_tools = registry.get_all()
        names = [t.name for t in all_tools]

        expected = [
            "calculator",
            "current_datetime",
            "json_formatter",
            "code_execution",
            "web_search",
            "http_request",
            "file_read",
            "file_write",
        ]
        for name in expected:
            assert name in names, f"Missing builtin tool: {name}"

    def test_tool_risk_classifications(self):
        """Verify risk levels match expected classifications."""
        from kovrin.tools.builtin import register_all_builtins

        registry = ToolRegistry()
        register_all_builtins(registry)

        # LOW risk tools
        for name in ["calculator", "current_datetime", "json_formatter"]:
            tool = registry.get(name)
            assert tool.risk_profile.risk_level == RiskLevel.LOW, f"{name} should be LOW risk"

        # File write should be MEDIUM+
        file_write = registry.get("file_write")
        assert file_write.risk_profile.risk_level in (
            RiskLevel.MEDIUM,
            RiskLevel.HIGH,
        ), "file_write should be MEDIUM or HIGH risk"
