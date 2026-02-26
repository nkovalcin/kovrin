"""End-to-end tests for the Merkle audit trail system.

Tests the ImmutableTraceLog's integrity guarantees: append-only,
tamper-evident, verifiable hash chain across pipeline operations.
"""

import hashlib

import pytest

from kovrin.audit.trace_logger import HashedTrace, ImmutableTraceLog
from kovrin.core.models import RiskLevel, Trace


# ─── Hash Chain Basics ───────────────────────────────────────


class TestHashChainBasics:
    """Fundamental Merkle chain properties."""

    def test_empty_chain_is_valid(self):
        log = ImmutableTraceLog()
        valid, _ = log.verify_integrity()
        assert valid is True
        assert len(log.get_events()) == 0

    def test_single_event_chain(self):
        log = ImmutableTraceLog()
        log.append(
            Trace(intent_id="i-1", event_type="TEST", description="First event")
        )
        valid, _ = log.verify_integrity()
        assert valid is True
        assert len(log.get_events()) == 1

    def test_multiple_events_chain(self):
        log = ImmutableTraceLog()
        for i in range(10):
            log.append(
                Trace(
                    intent_id="i-1",
                    event_type=f"EVENT_{i}",
                    description=f"Event {i}",
                )
            )
        valid, _ = log.verify_integrity()
        assert valid is True
        assert len(log.get_events()) == 10

    def test_events_are_ordered(self):
        """Events come back in insertion order."""
        log = ImmutableTraceLog()
        for i in range(5):
            log.append(
                Trace(intent_id="i-1", event_type=f"E{i}", description=f"Event {i}")
            )

        events = log.get_events()
        for i, event in enumerate(events):
            assert event.trace.event_type == f"E{i}"


# ─── Tamper Detection ────────────────────────────────────────


class TestTamperDetection:
    """Tampering with any event should break the chain."""

    def test_modifying_event_breaks_chain(self):
        log = ImmutableTraceLog()
        for i in range(5):
            log.append(
                Trace(intent_id="i-1", event_type=f"E{i}", description=f"Event {i}")
            )
        valid, _ = log.verify_integrity()
        assert valid is True

        # Tamper with an event in the middle
        events = log.get_events()
        # Directly modify the internal trace description (simulating tampering)
        # Trace is frozen (Pydantic), so bypass with object.__setattr__
        original_desc = events[2].trace.description
        object.__setattr__(events[2].trace, "description", "TAMPERED EVENT")

        # Integrity check should now FAIL
        valid, _ = log.verify_integrity()
        assert valid is False

        # Restore for cleanup
        object.__setattr__(events[2].trace, "description", original_desc)

    def test_hash_chain_linkage(self):
        """Each hash depends on the previous hash (chain linkage)."""
        log = ImmutableTraceLog()
        for i in range(3):
            log.append(
                Trace(intent_id="i-1", event_type=f"E{i}", description=f"Event {i}")
            )

        events = log.get_events()

        # First event's previous_hash should be genesis hash
        assert events[0].previous_hash == ImmutableTraceLog.GENESIS_HASH

        # Each subsequent event's previous_hash should match the previous event's hash
        for i in range(1, len(events)):
            assert events[i].previous_hash == events[i - 1].hash


# ─── Async Append ────────────────────────────────────────────


class TestAsyncAppend:
    """Async append maintains chain integrity."""

    @pytest.mark.asyncio
    async def test_async_append_single(self):
        log = ImmutableTraceLog()
        await log.append_async(
            Trace(intent_id="i-1", event_type="ASYNC_TEST", description="Async event")
        )
        valid, _ = log.verify_integrity()
        assert valid is True
        assert len(log.get_events()) == 1

    @pytest.mark.asyncio
    async def test_async_append_multiple(self):
        log = ImmutableTraceLog()
        for i in range(20):
            await log.append_async(
                Trace(intent_id="i-1", event_type=f"ASYNC_{i}", description=f"Event {i}")
            )
        valid, _ = log.verify_integrity()
        assert valid is True
        assert len(log.get_events()) == 20


# ─── Subscriber System ──────────────────────────────────────


class TestSubscriberSystem:
    """Subscribers receive events in real-time."""

    @pytest.mark.asyncio
    async def test_subscriber_receives_events(self):
        log = ImmutableTraceLog()
        received: list[HashedTrace] = []

        async def on_event(hashed: HashedTrace) -> None:
            received.append(hashed)

        log.subscribe(on_event)

        await log.append_async(
            Trace(intent_id="i-1", event_type="SUB_TEST", description="Test")
        )

        assert len(received) == 1
        assert received[0].trace.event_type == "SUB_TEST"

        log.unsubscribe(on_event)

    @pytest.mark.asyncio
    async def test_unsubscribed_stops_receiving(self):
        log = ImmutableTraceLog()
        received: list[HashedTrace] = []

        async def on_event(hashed: HashedTrace) -> None:
            received.append(hashed)

        log.subscribe(on_event)

        await log.append_async(
            Trace(intent_id="i-1", event_type="E1", description="Before unsub")
        )
        assert len(received) == 1

        log.unsubscribe(on_event)

        await log.append_async(
            Trace(intent_id="i-1", event_type="E2", description="After unsub")
        )
        # Should still be 1
        assert len(received) == 1

    @pytest.mark.asyncio
    async def test_multiple_subscribers(self):
        log = ImmutableTraceLog()
        received_a: list[HashedTrace] = []
        received_b: list[HashedTrace] = []

        async def sub_a(hashed: HashedTrace) -> None:
            received_a.append(hashed)

        async def sub_b(hashed: HashedTrace) -> None:
            received_b.append(hashed)

        log.subscribe(sub_a)
        log.subscribe(sub_b)

        await log.append_async(
            Trace(intent_id="i-1", event_type="MULTI", description="Both see this")
        )

        assert len(received_a) == 1
        assert len(received_b) == 1

        log.unsubscribe(sub_a)
        log.unsubscribe(sub_b)


# ─── Pipeline Trace Completeness ─────────────────────────────


class TestPipelineTraceCompleteness:
    """Verify that a complete pipeline produces the expected trace sequence."""

    @pytest.mark.asyncio
    async def test_full_pipeline_trace_sequence(self):
        """Simulate a full pipeline and verify trace event ordering."""
        log = ImmutableTraceLog()

        # Simulate the pipeline trace sequence
        events = [
            ("INTENT_RECEIVED", "Intent: Analyze expenses"),
            ("DECOMPOSITION", "Decomposed into 2 sub-tasks"),
            ("CRITIC_PIPELINE", "PASSED: Analyze data"),
            ("CRITIC_PIPELINE", "PASSED: Summarize findings"),
            ("GRAPH_OPTIMIZATION", "Graph optimized: parallel execution"),
            ("EXECUTION_START", "Executing 2 tasks across 1 wave"),
            ("EXECUTION_COMPLETE", "Task t-1 completed"),
            ("EXECUTION_COMPLETE", "Task t-2 completed"),
            ("PIPELINE_COMPLETE", "Pipeline complete: 2/2 tasks succeeded"),
        ]

        for event_type, description in events:
            await log.append_async(
                Trace(
                    intent_id="pipeline-1",
                    event_type=event_type,
                    description=description,
                )
            )

        valid, _ = log.verify_integrity()
        assert valid is True

        logged = log.get_events()
        assert len(logged) == 9
        assert logged[0].trace.event_type == "INTENT_RECEIVED"
        assert logged[-1].trace.event_type == "PIPELINE_COMPLETE"

    @pytest.mark.asyncio
    async def test_rejected_pipeline_trace_sequence(self):
        """Rejected pipeline produces appropriate trace events."""
        log = ImmutableTraceLog()

        events = [
            ("INTENT_RECEIVED", "Intent: Do something dangerous"),
            ("DECOMPOSITION", "Decomposed into 1 sub-task"),
            ("CRITIC_PIPELINE", "REJECTED: Dangerous action"),
            ("PIPELINE_ABORTED", "All sub-tasks rejected"),
        ]

        for event_type, description in events:
            await log.append_async(
                Trace(intent_id="rejected-1", event_type=event_type, description=description)
            )

        valid, _ = log.verify_integrity()
        assert valid is True

        logged = log.get_events()
        assert logged[-1].trace.event_type == "PIPELINE_ABORTED"

    @pytest.mark.asyncio
    async def test_mixed_intent_traces(self):
        """Multiple intents in the same log maintain integrity."""
        log = ImmutableTraceLog()

        for intent_num in range(3):
            intent_id = f"intent-{intent_num}"
            await log.append_async(
                Trace(intent_id=intent_id, event_type="INTENT_RECEIVED", description=f"Intent {intent_num}")
            )
            await log.append_async(
                Trace(intent_id=intent_id, event_type="PIPELINE_COMPLETE", description="Done")
            )

        valid, _ = log.verify_integrity()
        assert valid is True
        assert len(log.get_events()) == 6


# ─── Trace Data Integrity ───────────────────────────────────


class TestTraceDataIntegrity:
    """Verify trace data is preserved correctly."""

    def test_trace_details_preserved(self):
        log = ImmutableTraceLog()
        log.append(
            Trace(
                intent_id="i-1",
                event_type="DETAILED",
                description="With details",
                details={
                    "model": "claude-sonnet-4-6",
                    "cost_usd": 0.0015,
                    "input_tokens": 500,
                    "output_tokens": 200,
                },
                risk_level=RiskLevel.MEDIUM,
            )
        )

        event = log.get_events()[0]
        assert event.trace.details["model"] == "claude-sonnet-4-6"
        assert event.trace.details["cost_usd"] == 0.0015
        assert event.trace.risk_level == RiskLevel.MEDIUM

    def test_trace_task_id_preserved(self):
        log = ImmutableTraceLog()
        log.append(
            Trace(
                intent_id="i-1",
                task_id="t-42",
                event_type="TASK_EVENT",
                description="Task-specific event",
            )
        )

        event = log.get_events()[0]
        assert event.trace.task_id == "t-42"

    def test_trace_l0_passed_preserved(self):
        log = ImmutableTraceLog()
        log.append(
            Trace(
                intent_id="i-1",
                event_type="CRITIC_PIPELINE",
                description="L0 check",
                l0_passed=False,
            )
        )

        event = log.get_events()[0]
        assert event.trace.l0_passed is False


# ─── Large Scale ─────────────────────────────────────────────


class TestLargeScale:
    """Verify hash chain works at scale."""

    def test_1000_events(self):
        log = ImmutableTraceLog()
        for i in range(1000):
            log.append(
                Trace(
                    intent_id=f"i-{i % 10}",
                    event_type="SCALE_TEST",
                    description=f"Event {i}",
                    details={"index": i},
                )
            )

        valid, _ = log.verify_integrity()
        assert valid is True
        assert len(log.get_events()) == 1000
