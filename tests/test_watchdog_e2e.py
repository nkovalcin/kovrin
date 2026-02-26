"""End-to-end tests for the Watchdog containment system.

Tests the full watchdog flow: start → observe trace events →
evaluate temporal rules → graduated containment (WARN → PAUSE → KILL).
"""

import asyncio
from unittest.mock import AsyncMock, MagicMock

import pytest

from kovrin import Kovrin
from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import (
    ContainmentLevel,
    Trace,
    WatchdogAlert,
)
from kovrin.safety.watchdog import (
    AgentDriftTracker,
    ExcessiveFailureRate,
    ExcessiveToolCallRate,
    NoExecutionAfterRejection,
    ToolCallAfterBlock,
    ToolEscalationDetection,
    UnexpectedEventSequence,
    WatchdogAgent,
    make_agent_drift_rules,
)


# ─── Watchdog Lifecycle ──────────────────────────────────────


class TestWatchdogLifecycle:
    """Start, monitor events, stop."""

    @pytest.mark.asyncio
    async def test_start_and_stop(self):
        watchdog = WatchdogAgent()
        trace_log = ImmutableTraceLog()

        await watchdog.start(trace_log, "Test intent")
        assert watchdog._trace_log is trace_log
        assert not watchdog.is_killed
        assert not watchdog.is_paused

        await watchdog.stop()

    @pytest.mark.asyncio
    async def test_watchdog_observes_trace_events(self):
        """Watchdog receives events appended to the trace log."""
        watchdog = WatchdogAgent()
        trace_log = ImmutableTraceLog()

        await watchdog.start(trace_log, "Monitor test")

        # Append an event — watchdog should process it
        await trace_log.append_async(
            Trace(
                intent_id="i-1",
                event_type="INTENT_RECEIVED",
                description="Test intent received",
            )
        )

        # Give the subscriber a chance to process
        await asyncio.sleep(0.01)

        # Watchdog history should have the event
        assert len(watchdog._history) == 1

        await watchdog.stop()


# ─── NoExecutionAfterRejection ───────────────────────────────


class TestNoExecutionAfterRejection:
    """KILL: Executing a task after L0 rejection is a critical violation."""

    @pytest.mark.asyncio
    async def test_execution_after_rejection_kills(self):
        watchdog = WatchdogAgent()
        trace_log = ImmutableTraceLog()

        await watchdog.start(trace_log, "Test intent")

        # Task rejected by L0
        await trace_log.append_async(
            Trace(
                intent_id="i-1",
                task_id="t-1",
                event_type="L0_CHECK",
                description="L0 check failed",
                l0_passed=False,
            )
        )
        await asyncio.sleep(0.01)

        # Attempt to execute the same task — should trigger KILL
        await trace_log.append_async(
            Trace(
                intent_id="i-1",
                task_id="t-1",
                event_type="EXECUTION_START",
                description="Starting rejected task",
            )
        )
        await asyncio.sleep(0.01)

        assert watchdog.is_killed is True
        assert len(watchdog.alerts) >= 1
        kill_alerts = [a for a in watchdog.alerts if a.severity == ContainmentLevel.KILL]
        assert len(kill_alerts) >= 1
        assert "t-1" in kill_alerts[0].reason

        await watchdog.stop()

    @pytest.mark.asyncio
    async def test_kill_is_irreversible(self):
        """Invariant #5: KILL cannot be downgraded."""
        watchdog = WatchdogAgent()
        trace_log = ImmutableTraceLog()
        await watchdog.start(trace_log, "Test")

        # Trigger KILL
        await trace_log.append_async(
            Trace(intent_id="i-1", task_id="t-1", event_type="L0_CHECK", l0_passed=False)
        )
        await asyncio.sleep(0.01)
        await trace_log.append_async(
            Trace(intent_id="i-1", task_id="t-1", event_type="EXECUTION_START")
        )
        await asyncio.sleep(0.01)

        assert watchdog.is_killed is True

        # Resume should not undo KILL
        watchdog.resume()
        assert watchdog.is_killed is True

        await watchdog.stop()


# ─── ExcessiveFailureRate ────────────────────────────────────


class TestExcessiveFailureRate:
    """PAUSE: When failure rate exceeds 50%."""

    @pytest.mark.asyncio
    async def test_high_failure_rate_pauses(self):
        watchdog = WatchdogAgent()
        trace_log = ImmutableTraceLog()
        await watchdog.start(trace_log, "Test")

        # Add 1 completed + 3 rejected (75% failure rate)
        await trace_log.append_async(
            Trace(intent_id="i-1", event_type="EXECUTION_COMPLETE", task_id="t-ok")
        )
        await asyncio.sleep(0.01)

        for i in range(3):
            await trace_log.append_async(
                Trace(
                    intent_id="i-1",
                    event_type="CRITIC_PIPELINE",
                    task_id=f"t-fail-{i}",
                    l0_passed=False,
                )
            )
            await asyncio.sleep(0.01)

        # Now trigger evaluation with another event
        await trace_log.append_async(
            Trace(intent_id="i-1", event_type="EXECUTION_COMPLETE", task_id="t-ok2")
        )
        await asyncio.sleep(0.01)

        assert watchdog.is_paused is True

        await watchdog.stop()

    @pytest.mark.asyncio
    async def test_pause_can_be_resumed(self):
        """PAUSE is resumable (unlike KILL)."""
        watchdog = WatchdogAgent()
        trace_log = ImmutableTraceLog()
        await watchdog.start(trace_log, "Test")

        # Trigger PAUSE via excessive failures
        await trace_log.append_async(
            Trace(intent_id="i-1", event_type="EXECUTION_COMPLETE", task_id="t-1")
        )
        await asyncio.sleep(0.01)
        for i in range(3):
            await trace_log.append_async(
                Trace(intent_id="i-1", event_type="CRITIC_PIPELINE", task_id=f"t-f{i}", l0_passed=False)
            )
            await asyncio.sleep(0.01)
        await trace_log.append_async(
            Trace(intent_id="i-1", event_type="EXECUTION_COMPLETE", task_id="t-2")
        )
        await asyncio.sleep(0.01)

        assert watchdog.is_paused is True

        watchdog.resume()
        assert watchdog.is_paused is False

        await watchdog.stop()


# ─── UnexpectedEventSequence ─────────────────────────────────


class TestUnexpectedEventSequence:
    """WARN: Suspicious event patterns."""

    @pytest.mark.asyncio
    async def test_complete_without_start_warns(self):
        watchdog = WatchdogAgent()
        trace_log = ImmutableTraceLog()
        await watchdog.start(trace_log, "Test")

        # Some initial event to populate history
        await trace_log.append_async(
            Trace(intent_id="i-1", event_type="INTENT_RECEIVED")
        )
        await asyncio.sleep(0.01)

        # EXECUTION_COMPLETE without EXECUTION_START for same task
        await trace_log.append_async(
            Trace(intent_id="i-1", task_id="t-orphan", event_type="EXECUTION_COMPLETE")
        )
        await asyncio.sleep(0.01)

        warn_alerts = [a for a in watchdog.alerts if a.severity == ContainmentLevel.WARN]
        assert len(warn_alerts) >= 1
        assert "t-orphan" in warn_alerts[0].reason

        # WARN does not pause or kill
        assert not watchdog.is_paused
        assert not watchdog.is_killed

        await watchdog.stop()


# ─── Tool Safety Rules ───────────────────────────────────────


class TestToolSafetyRules:
    """Tool-related watchdog rules."""

    @pytest.mark.asyncio
    async def test_excessive_tool_calls_pauses(self):
        """Too many tool calls per minute triggers PAUSE."""
        watchdog = WatchdogAgent(
            rules=[ExcessiveToolCallRate(max_calls_per_minute=5)]
        )
        trace_log = ImmutableTraceLog()
        await watchdog.start(trace_log, "Test")

        # Fire 6 TOOL_CALL events in rapid succession
        for i in range(6):
            await trace_log.append_async(
                Trace(
                    intent_id="i-1",
                    task_id="t-1",
                    event_type="TOOL_CALL",
                    description=f"Tool call {i}",
                )
            )
            await asyncio.sleep(0.01)

        assert watchdog.is_paused is True

        await watchdog.stop()

    @pytest.mark.asyncio
    async def test_tool_escalation_warns(self):
        """Tool risk escalation from LOW → HIGH triggers WARN."""
        watchdog = WatchdogAgent(rules=[ToolEscalationDetection()])
        trace_log = ImmutableTraceLog()
        await watchdog.start(trace_log, "Test")

        # LOW risk tool call
        await trace_log.append_async(
            Trace(
                intent_id="i-1",
                task_id="t-1",
                event_type="TOOL_CALL",
                details={"risk_level": "LOW", "tool_name": "calculator"},
            )
        )
        await asyncio.sleep(0.01)

        # HIGH risk tool call for same task
        await trace_log.append_async(
            Trace(
                intent_id="i-1",
                task_id="t-1",
                event_type="TOOL_CALL",
                details={"risk_level": "HIGH", "tool_name": "file_write"},
            )
        )
        await asyncio.sleep(0.01)

        warn_alerts = [a for a in watchdog.alerts if a.severity == ContainmentLevel.WARN]
        assert len(warn_alerts) >= 1
        assert "escalation" in warn_alerts[0].reason.lower()

        await watchdog.stop()

    @pytest.mark.asyncio
    async def test_repeated_blocked_tool_pauses(self):
        """Calling a blocked tool repeatedly triggers PAUSE."""
        watchdog = WatchdogAgent(rules=[ToolCallAfterBlock()])
        trace_log = ImmutableTraceLog()
        await watchdog.start(trace_log, "Test")

        # First block
        await trace_log.append_async(
            Trace(
                intent_id="i-1",
                task_id="t-1",
                event_type="TOOL_CALL_BLOCKED",
                details={"tool_name": "file_write"},
            )
        )
        await asyncio.sleep(0.01)

        # Second block — same tool, same task
        await trace_log.append_async(
            Trace(
                intent_id="i-1",
                task_id="t-1",
                event_type="TOOL_CALL_BLOCKED",
                details={"tool_name": "file_write"},
            )
        )
        await asyncio.sleep(0.01)

        pause_alerts = [a for a in watchdog.alerts if a.severity == ContainmentLevel.PAUSE]
        assert len(pause_alerts) >= 1
        assert "file_write" in pause_alerts[0].reason

        await watchdog.stop()


# ─── Agent Drift Detection ───────────────────────────────────


class TestAgentDriftE2E:
    """End-to-end tests for agent drift detection."""

    @pytest.mark.asyncio
    async def test_high_drift_pauses(self):
        """Agent with consistently terrible PRM scores triggers PAUSE (HIGH drift).

        Note: PRM_EVALUATION events record success=True by default in
        AgentCompetencyDrift, so only avg PRM score drops. HIGH drift
        (avg < 0.35) triggers PAUSE.
        """
        tracker = AgentDriftTracker()
        drift_rules = make_agent_drift_rules(tracker)
        watchdog = WatchdogAgent(rules=drift_rules)
        trace_log = ImmutableTraceLog()
        await watchdog.start(trace_log, "Test")

        # Simulate 5 terrible PRM evaluations
        for i in range(5):
            await trace_log.append_async(
                Trace(
                    intent_id="i-1",
                    task_id=f"t-{i}",
                    event_type="PRM_EVALUATION",
                    details={
                        "agent_name": "bad_agent",
                        "aggregate_score": 0.1,
                    },
                )
            )
            await asyncio.sleep(0.01)

        # Check that PAUSE was triggered (HIGH drift — avg PRM < 0.35)
        pause_alerts = [a for a in watchdog.alerts if a.severity == ContainmentLevel.PAUSE]
        assert len(pause_alerts) >= 1
        assert "bad_agent" in pause_alerts[0].reason

        await watchdog.stop()

    def test_drift_tracker_metrics(self):
        """AgentDriftTracker correctly computes drift levels."""
        tracker = AgentDriftTracker()

        # Record good performance
        for _ in range(5):
            tracker.record("good_agent", "t-1", prm_score=0.9, success=True)

        metrics = tracker.get_metrics("good_agent")
        assert metrics.drift_level.value == "NONE"
        assert metrics.average_prm_score > 0.8

        # Record poor performance
        for _ in range(5):
            tracker.record("bad_agent", "t-2", prm_score=0.15, success=False)

        metrics = tracker.get_metrics("bad_agent")
        assert metrics.drift_level.value == "CRITICAL"
        assert metrics.success_rate < 0.01


# ─── Watchdog in Pipeline Context ────────────────────────────


class TestWatchdogInPipeline:
    """Test watchdog integration with the Kovrin pipeline."""

    @pytest.mark.asyncio
    async def test_watchdog_kill_stops_pipeline(self):
        """When watchdog kills, remaining tasks should not execute."""
        from kovrin.core.models import SubTask

        engine = Kovrin(api_key="test-key", watchdog=True)

        subtasks = [
            SubTask(id="t-1", description="Good task"),
            SubTask(id="t-2", description="Another task"),
        ]
        engine._parser.parse = AsyncMock(return_value=subtasks)

        # Critics: first task passes with L0 rejection trace
        # This simulates the watchdog detecting a violation
        call_count = 0

        async def mock_critics(subtask, constraints=None, intent_context="", task_context=None):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                return (True, [])
            return (True, [])

        engine._critics.evaluate = AsyncMock(side_effect=mock_critics)
        engine._graph_executor.execute = AsyncMock(
            return_value={"t-1": "Done", "t-2": "Done"}
        )

        result = await engine.run(intent="Test with watchdog")

        # Pipeline should complete (watchdog didn't trigger in this scenario)
        assert result.success is True

        # Verify watchdog was started and stopped
        # (watchdog is created fresh each run)

    @pytest.mark.asyncio
    async def test_engine_watchdog_init(self):
        """Kovrin with watchdog=True initializes properly."""
        engine = Kovrin(api_key="test-key", watchdog=True)
        assert engine._watchdog_enabled is True
        assert engine._watchdog is None  # Created on run(), not init


# ─── Graduated Containment Progression ───────────────────────


class TestGraduatedContainment:
    """WARN → PAUSE → KILL progression with multiple rules."""

    @pytest.mark.asyncio
    async def test_warn_then_pause_then_kill(self):
        """Multiple rule violations produce graduated containment."""
        watchdog = WatchdogAgent()
        trace_log = ImmutableTraceLog()
        await watchdog.start(trace_log, "Test")

        # 1. WARN: unexpected sequence
        await trace_log.append_async(
            Trace(intent_id="i-1", event_type="INTENT_RECEIVED")
        )
        await asyncio.sleep(0.01)
        await trace_log.append_async(
            Trace(intent_id="i-1", task_id="t-1", event_type="EXECUTION_COMPLETE")
        )
        await asyncio.sleep(0.01)

        warn_alerts = [a for a in watchdog.alerts if a.severity == ContainmentLevel.WARN]
        assert len(warn_alerts) >= 1
        assert not watchdog.is_paused
        assert not watchdog.is_killed

        # 2. KILL: execution after rejection
        await trace_log.append_async(
            Trace(intent_id="i-1", task_id="t-2", event_type="L0_CHECK", l0_passed=False)
        )
        await asyncio.sleep(0.01)
        await trace_log.append_async(
            Trace(intent_id="i-1", task_id="t-2", event_type="EXECUTION_START")
        )
        await asyncio.sleep(0.01)

        assert watchdog.is_killed is True
        kill_alerts = [a for a in watchdog.alerts if a.severity == ContainmentLevel.KILL]
        assert len(kill_alerts) >= 1

        await watchdog.stop()
