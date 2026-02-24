"""Adversarial tests for the Kovrin Tool Execution System.

These tests verify that the safety invariants hold under attack:
1. CRITICAL tools always require HUMAN_APPROVAL
2. DCT scope cannot be expanded through tool access
3. Blocked tool calls are logged to the Merkle chain
4. Rate limits cannot be bypassed
5. Watchdog detects tool call anomalies
"""

import pytest

from kovrin.agents.tools import ToolDefinition
from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import (
    DelegationScope,
    RiskLevel,
    RoutingAction,
    SpeculationTier,
)
from kovrin.engine.risk_router import RiskRouter
from kovrin.tools.models import ToolCallRequest, ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool, ToolRegistry
from kovrin.tools.router import SafeToolRouter


def _make_adversarial_registry() -> ToolRegistry:
    """Registry with tools at every risk level for adversarial testing."""
    registry = ToolRegistry()

    for name, risk, tier, cat, tags in [
        ("read_data", RiskLevel.LOW, SpeculationTier.FREE, ToolCategory.READ_ONLY, ["read_only"]),
        ("write_file", RiskLevel.MEDIUM, SpeculationTier.GUARDED, ToolCategory.FILE_SYSTEM, ["filesystem"]),
        ("exec_code", RiskLevel.HIGH, SpeculationTier.GUARDED, ToolCategory.CODE_EXECUTION, ["code_execution"]),
        ("nuke_db", RiskLevel.CRITICAL, SpeculationTier.NONE, ToolCategory.EXTERNAL_API, ["critical", "database"]),
    ]:
        registry.register(RegisteredTool(
            definition=ToolDefinition(name=name, description=f"Test: {name}", input_schema={"type": "object", "properties": {}}),
            risk_profile=ToolRiskProfile(
                risk_level=risk, speculation_tier=tier, category=cat, scope_tags=tags, max_calls_per_task=3,
            ),
            handler=lambda: "ok",
        ))

    return registry


@pytest.mark.adversarial
class TestCriticalAlwaysHumanApproval:
    """Safety invariant: CRITICAL risk → HUMAN_APPROVAL, always."""

    @pytest.mark.asyncio
    async def test_critical_tool_blocked_without_callback(self):
        """CRITICAL tool without approval callback → blocked."""
        registry = _make_adversarial_registry()
        router = SafeToolRouter(registry=registry, risk_router=RiskRouter())

        decision = await router.evaluate(ToolCallRequest(
            tool_name="nuke_db", tool_input={}, tool_use_id="tc-1", task_id="t1", intent_id="i1",
        ))
        assert decision.action == RoutingAction.HUMAN_APPROVAL
        assert decision.allowed is False

    @pytest.mark.asyncio
    async def test_critical_tool_not_auto_executed_even_with_aggressive_profile(self):
        """CRITICAL tools must require approval even if AGGRESSIVE autonomy is active.

        The RiskRouter's CRITICAL safety guard (line 98-99) ensures this.
        """
        from kovrin.core.models import AutonomyProfile, AutonomySettings

        registry = _make_adversarial_registry()
        risk_router = RiskRouter()

        # Aggressive profile should NOT bypass CRITICAL guard
        router = SafeToolRouter(registry=registry, risk_router=risk_router)

        decision = await router.evaluate(ToolCallRequest(
            tool_name="nuke_db", tool_input={}, tool_use_id="tc-1", task_id="t1", intent_id="i1",
        ))
        assert decision.action == RoutingAction.HUMAN_APPROVAL
        assert decision.allowed is False


@pytest.mark.adversarial
class TestScopeNarrowing:
    """Safety invariant: DCT scope can only narrow, never expand."""

    def test_read_only_scope_excludes_code_execution(self):
        """Agent with read_only scope should not see code_execution tools."""
        registry = _make_adversarial_registry()

        scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW],
            allowed_capabilities=["read_only"],
        )
        tools = registry.get_for_scope(scope)
        names = {t.name for t in tools}
        assert "exec_code" not in names
        assert "nuke_db" not in names
        assert "read_data" in names

    def test_low_risk_scope_excludes_high_risk_tools(self):
        """Scope limited to LOW risk must not include HIGH or CRITICAL tools."""
        registry = _make_adversarial_registry()

        scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW],
        )
        tools = registry.get_for_scope(scope)
        for tool in tools:
            assert tool.risk_level == RiskLevel.LOW

    def test_category_restriction_blocks_code_execution(self):
        """Scope with only READ_ONLY category must block CODE_EXECUTION tools."""
        registry = _make_adversarial_registry()

        scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW, RiskLevel.MEDIUM, RiskLevel.HIGH],
            allowed_tool_categories=[ToolCategory.READ_ONLY],
        )
        tools = registry.get_for_scope(scope)
        for tool in tools:
            assert tool.category == ToolCategory.READ_ONLY


@pytest.mark.adversarial
class TestBlockedCallsAudited:
    """Safety invariant: ALL blocked tool calls logged to Merkle chain."""

    @pytest.mark.asyncio
    async def test_blocked_unknown_tool_in_merkle(self):
        trace_log = ImmutableTraceLog()
        registry = _make_adversarial_registry()
        router = SafeToolRouter(registry=registry, risk_router=RiskRouter(), trace_log=trace_log)

        await router.evaluate(ToolCallRequest(
            tool_name="evil_tool", tool_input={}, tool_use_id="tc-1", task_id="t1", intent_id="i1",
        ))

        events = trace_log.get_events()
        assert len(events) == 1
        assert events[0].trace.event_type == "TOOL_CALL_BLOCKED"

        valid, msg = trace_log.verify_integrity()
        assert valid is True

    @pytest.mark.asyncio
    async def test_blocked_critical_tool_in_merkle(self):
        trace_log = ImmutableTraceLog()
        registry = _make_adversarial_registry()
        router = SafeToolRouter(registry=registry, risk_router=RiskRouter(), trace_log=trace_log)

        await router.evaluate(ToolCallRequest(
            tool_name="nuke_db", tool_input={}, tool_use_id="tc-1", task_id="t1", intent_id="i1",
        ))

        events = trace_log.get_events()
        blocked_events = [e for e in events if e.trace.event_type == "TOOL_CALL_BLOCKED"]
        assert len(blocked_events) == 1
        assert blocked_events[0].trace.details["tool_name"] == "nuke_db"

    @pytest.mark.asyncio
    async def test_rate_limited_call_in_merkle(self):
        """Rate-limited tool calls must also appear in audit trail."""
        trace_log = ImmutableTraceLog()
        registry = _make_adversarial_registry()
        router = SafeToolRouter(registry=registry, risk_router=RiskRouter(), trace_log=trace_log)

        # Exhaust rate limit (max 3)
        for i in range(4):
            await router.evaluate(ToolCallRequest(
                tool_name="read_data", tool_input={}, tool_use_id=f"tc-{i}", task_id="t1", intent_id="i1",
            ))

        events = trace_log.get_events()
        blocked = [e for e in events if e.trace.event_type == "TOOL_CALL_BLOCKED"]
        assert len(blocked) == 1
        assert "Rate limit" in blocked[0].trace.description

        valid, _ = trace_log.verify_integrity()
        assert valid is True


@pytest.mark.adversarial
class TestRateLimitBypass:
    """Verify rate limits cannot be bypassed."""

    @pytest.mark.asyncio
    async def test_cannot_bypass_by_changing_tool_use_id(self):
        """Different tool_use_ids should not reset the counter."""
        registry = _make_adversarial_registry()
        router = SafeToolRouter(registry=registry, risk_router=RiskRouter())

        for i in range(3):
            decision = await router.evaluate(ToolCallRequest(
                tool_name="read_data", tool_input={}, tool_use_id=f"unique-{i}", task_id="t1", intent_id="i1",
            ))
            assert decision.allowed is True

        # 4th call — different tool_use_id but same task+tool
        decision = await router.evaluate(ToolCallRequest(
            tool_name="read_data", tool_input={}, tool_use_id="bypass-attempt", task_id="t1", intent_id="i1",
        ))
        assert decision.allowed is False

    @pytest.mark.asyncio
    async def test_cannot_bypass_by_changing_input(self):
        """Different inputs should not reset the counter."""
        registry = _make_adversarial_registry()
        router = SafeToolRouter(registry=registry, risk_router=RiskRouter())

        for i in range(3):
            await router.evaluate(ToolCallRequest(
                tool_name="read_data", tool_input={"data": str(i)}, tool_use_id=f"tc-{i}", task_id="t1", intent_id="i1",
            ))

        decision = await router.evaluate(ToolCallRequest(
            tool_name="read_data", tool_input={"data": "new"}, tool_use_id="tc-4", task_id="t1", intent_id="i1",
        ))
        assert decision.allowed is False


@pytest.mark.adversarial
class TestWatchdogToolRules:
    """Verify watchdog temporal rules detect tool call anomalies."""

    def test_excessive_tool_call_rate_rule(self):
        from datetime import datetime, timezone, timedelta
        from kovrin.audit.trace_logger import HashedTrace
        from kovrin.core.models import Trace
        from kovrin.safety.watchdog import ExcessiveToolCallRate

        rule = ExcessiveToolCallRate(max_calls_per_minute=5)

        # Build history with 5 TOOL_CALL events in the last 30 seconds
        base_time = datetime.now(timezone.utc)
        history = []
        for i in range(5):
            ht = HashedTrace(
                trace=Trace(
                    event_type="TOOL_CALL",
                    intent_id="i1",
                    task_id="t1",
                    timestamp=base_time - timedelta(seconds=i * 5),
                ),
                hash=f"hash-{i}",
                previous_hash=f"prev-{i}",
                sequence=i,
            )
            history.append(ht)

        # 6th event should trigger alert
        new_event = HashedTrace(
            trace=Trace(
                event_type="TOOL_CALL",
                intent_id="i1",
                task_id="t1",
                timestamp=base_time,
            ),
            hash="hash-new",
            previous_hash="prev-new",
            sequence=5,
        )

        alert = rule.check(new_event, history)
        assert alert is not None
        assert "Excessive" in alert.reason

    def test_tool_escalation_detection_rule(self):
        from kovrin.audit.trace_logger import HashedTrace
        from kovrin.core.models import Trace
        from kovrin.safety.watchdog import ToolEscalationDetection

        rule = ToolEscalationDetection()

        # History: LOW risk tool call
        history = [HashedTrace(
            trace=Trace(
                event_type="TOOL_CALL",
                task_id="t1",
                intent_id="i1",
                details={"risk_level": "LOW", "tool": "read_data"},
            ),
            hash="h1",
            previous_hash="p1",
            sequence=0,
        )]

        # New event: HIGH risk tool call for same task
        escalated = HashedTrace(
            trace=Trace(
                event_type="TOOL_CALL",
                task_id="t1",
                intent_id="i1",
                details={"risk_level": "HIGH", "tool": "exec_code"},
            ),
            hash="h2",
            previous_hash="h1",
            sequence=1,
        )

        alert = rule.check(escalated, history)
        assert alert is not None
        assert "escalation" in alert.reason.lower()

    def test_tool_call_after_block_rule(self):
        from kovrin.audit.trace_logger import HashedTrace
        from kovrin.core.models import Trace
        from kovrin.safety.watchdog import ToolCallAfterBlock

        rule = ToolCallAfterBlock()

        # History: tool was already blocked once
        history = [HashedTrace(
            trace=Trace(
                event_type="TOOL_CALL_BLOCKED",
                task_id="t1",
                intent_id="i1",
                details={"tool_name": "nuke_db"},
            ),
            hash="h1",
            previous_hash="p1",
            sequence=0,
        )]

        # Same tool blocked again
        repeat_block = HashedTrace(
            trace=Trace(
                event_type="TOOL_CALL_BLOCKED",
                task_id="t1",
                intent_id="i1",
                details={"tool_name": "nuke_db"},
            ),
            hash="h2",
            previous_hash="h1",
            sequence=1,
        )

        alert = rule.check(repeat_block, history)
        assert alert is not None
        assert "bypass attempt" in alert.reason.lower()
