"""
Tests for Drift Detection in the Watchdog Agent.

Verifies:
- ALIGNED response -> no alert
- DRIFTED response -> PAUSE alert
- UNCERTAIN response -> WARN alert
- Rate limiting (min interval between checks)
- API errors handled gracefully
- Only triggers on EXECUTION_COMPLETE events
"""

import asyncio
import time
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin.audit.trace_logger import HashedTrace, ImmutableTraceLog
from kovrin.core.models import ContainmentLevel, Trace, WatchdogAlert
from kovrin.safety.watchdog import WatchdogAgent


# ─── Helpers ────────────────────────────────────────────────


def make_hashed(event_type: str = "EXECUTION_COMPLETE", **kwargs) -> HashedTrace:
    defaults = {
        "intent_id": "test-intent",
        "task_id": "task-1",
        "event_type": event_type,
        "description": "Completed: Analyze market trends",
        "details": {"output_length": 500},
    }
    defaults.update(kwargs)
    trace = Trace(**defaults)
    return HashedTrace(
        trace=trace,
        hash="a" * 64,
        previous_hash="0" * 64,
        sequence=0,
    )


def make_mock_client(verdict: str, reason: str = "Test reason"):
    """Create a mock Anthropic client that returns a drift verdict."""
    client = MagicMock()
    response = MagicMock()
    response.content = [MagicMock(text=f"{verdict}\n{reason}")]
    client.messages = MagicMock()
    client.messages.create = AsyncMock(return_value=response)
    return client


# ─── Drift Detection Tests ─────────────────────────────────


class TestDriftDetection:
    @pytest.mark.asyncio
    async def test_aligned_no_alert(self):
        """ALIGNED verdict should produce no alert."""
        client = make_mock_client("ALIGNED", "Task aligns with intent")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Analyze market trends"

        event = make_hashed()
        alert = await watchdog._check_drift(event)
        assert alert is None

    @pytest.mark.asyncio
    async def test_drifted_pause_alert(self):
        """DRIFTED verdict should produce a PAUSE alert."""
        client = make_mock_client("DRIFTED", "Task diverged from original intent")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Analyze market trends"

        event = make_hashed()
        alert = await watchdog._check_drift(event)
        assert alert is not None
        assert alert.severity == ContainmentLevel.PAUSE
        assert "Drift detected" in alert.reason
        assert alert.rule == "drift_detection"

    @pytest.mark.asyncio
    async def test_uncertain_warn_alert(self):
        """UNCERTAIN verdict should produce a WARN alert."""
        client = make_mock_client("UNCERTAIN", "Cannot determine alignment")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Analyze market trends"

        event = make_hashed()
        alert = await watchdog._check_drift(event)
        assert alert is not None
        assert alert.severity == ContainmentLevel.WARN
        assert "Drift uncertain" in alert.reason

    @pytest.mark.asyncio
    async def test_api_error_no_alert(self):
        """API errors should not produce alerts."""
        client = MagicMock()
        client.messages = MagicMock()
        client.messages.create = AsyncMock(side_effect=Exception("API down"))
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Test intent"

        event = make_hashed()
        alert = await watchdog._check_drift(event)
        assert alert is None

    @pytest.mark.asyncio
    async def test_drift_check_includes_intent_context(self):
        """Drift check should pass the intent context to Claude."""
        client = make_mock_client("ALIGNED")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Compare microservices vs monolith"

        event = make_hashed()
        await watchdog._check_drift(event)

        # Verify the prompt contains the intent
        call_args = client.messages.create.call_args
        prompt = call_args.kwargs["messages"][0]["content"]
        assert "Compare microservices vs monolith" in prompt

    @pytest.mark.asyncio
    async def test_drift_alert_has_correct_fields(self):
        """Drift alert should include task_id and intent_id."""
        client = make_mock_client("DRIFTED", "Off topic")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Test intent"

        event = make_hashed(task_id="task-xyz", intent_id="intent-abc")
        alert = await watchdog._check_drift(event)
        assert alert.task_id == "task-xyz"
        assert alert.intent_id == "intent-abc"


class TestDriftRateLimiting:
    @pytest.mark.asyncio
    async def test_rate_limiting_skips_rapid_checks(self):
        """Drift check should be rate-limited."""
        client = make_mock_client("ALIGNED")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Test"
        watchdog._drift_check_interval = 1.0  # 1 second minimum

        log = ImmutableTraceLog()
        await watchdog.start(log, "Test intent")

        # First event — should trigger drift check
        event1 = make_hashed(task_id="task-1")
        await log.append_async(event1.trace)
        assert client.messages.create.call_count == 1

        # Second event immediately — should be rate-limited (skipped)
        event2 = make_hashed(task_id="task-2")
        await log.append_async(event2.trace)
        assert client.messages.create.call_count == 1  # Still 1

        await watchdog.stop()

    @pytest.mark.asyncio
    async def test_rate_limiting_allows_after_interval(self):
        """After the interval, drift check should proceed."""
        client = make_mock_client("ALIGNED")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Test"
        watchdog._drift_check_interval = 0.05  # Very short for testing

        log = ImmutableTraceLog()
        await watchdog.start(log, "Test intent")

        # First event
        await log.append_async(make_hashed(task_id="task-1").trace)
        assert client.messages.create.call_count == 1

        # Wait for interval
        await asyncio.sleep(0.1)

        # Second event — should pass rate limit
        await log.append_async(make_hashed(task_id="task-2").trace)
        assert client.messages.create.call_count == 2

        await watchdog.stop()


class TestDriftOnlyOnComplete:
    @pytest.mark.asyncio
    async def test_no_drift_check_on_start_event(self):
        """Drift detection should NOT trigger on EXECUTION_START."""
        client = make_mock_client("ALIGNED")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Test"

        log = ImmutableTraceLog()
        await watchdog.start(log, "Test intent")

        # EXECUTION_START should NOT trigger drift
        await log.append_async(Trace(
            intent_id="test",
            task_id="task-1",
            event_type="EXECUTION_START",
            description="Starting task",
        ))
        assert client.messages.create.call_count == 0

        await watchdog.stop()

    @pytest.mark.asyncio
    async def test_no_drift_check_on_decomposition(self):
        """Drift detection should NOT trigger on DECOMPOSITION."""
        client = make_mock_client("ALIGNED")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Test"

        log = ImmutableTraceLog()
        await watchdog.start(log, "Test intent")

        await log.append_async(Trace(
            intent_id="test",
            event_type="DECOMPOSITION",
            description="Decomposed",
        ))
        assert client.messages.create.call_count == 0

        await watchdog.stop()

    @pytest.mark.asyncio
    async def test_drift_check_on_execution_complete(self):
        """Drift detection SHOULD trigger on EXECUTION_COMPLETE."""
        client = make_mock_client("ALIGNED")
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Test"

        log = ImmutableTraceLog()
        await watchdog.start(log, "Test intent")

        await log.append_async(Trace(
            intent_id="test",
            task_id="task-1",
            event_type="EXECUTION_COMPLETE",
            description="Completed task",
            details={"output_length": 100},
        ))
        assert client.messages.create.call_count == 1

        await watchdog.stop()


class TestDriftDisabled:
    @pytest.mark.asyncio
    async def test_no_drift_when_disabled(self):
        """When enable_drift_detection=False, no drift checks happen."""
        client = make_mock_client("DRIFTED")
        watchdog = WatchdogAgent(
            enable_drift_detection=False,
            client=client,
            rules=[],
        )
        watchdog._intent_context = "Test"

        log = ImmutableTraceLog()
        await watchdog.start(log, "Test intent")

        await log.append_async(Trace(
            intent_id="test",
            task_id="task-1",
            event_type="EXECUTION_COMPLETE",
            description="Completed",
            details={"output_length": 100},
        ))
        assert client.messages.create.call_count == 0
        assert len(watchdog.alerts) == 0

        await watchdog.stop()

    @pytest.mark.asyncio
    async def test_no_drift_without_client(self):
        """When no client, drift checks are skipped."""
        watchdog = WatchdogAgent(
            enable_drift_detection=True,
            client=None,
            rules=[],
        )

        log = ImmutableTraceLog()
        await watchdog.start(log, "Test intent")

        await log.append_async(Trace(
            intent_id="test",
            task_id="task-1",
            event_type="EXECUTION_COMPLETE",
            description="Completed",
        ))
        assert len(watchdog.alerts) == 0

        await watchdog.stop()
