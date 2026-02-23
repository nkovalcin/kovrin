"""
Tests for real-time WebSocket streaming via ImmutableTraceLog subscribers.

Verifies that:
- append_async notifies subscribers
- Multiple subscribers all receive events
- Subscriber errors don't break the trace log
- Unsubscribe stops notifications
"""

import asyncio

import pytest

from kovrin.audit.trace_logger import ImmutableTraceLog, HashedTrace
from kovrin.core.models import Trace


# ─── Helpers ────────────────────────────────────────────────


def make_trace(**kwargs) -> Trace:
    defaults = {
        "intent_id": "test-intent",
        "event_type": "TEST_EVENT",
        "description": "Test event",
    }
    defaults.update(kwargs)
    return Trace(**defaults)


# ─── Tests ──────────────────────────────────────────────────


@pytest.mark.asyncio
async def test_append_async_notifies_subscriber():
    """append_async should notify registered subscribers."""
    log = ImmutableTraceLog()
    received: list[HashedTrace] = []

    async def callback(hashed: HashedTrace) -> None:
        received.append(hashed)

    log.subscribe(callback)
    await log.append_async(make_trace(description="event 1"))
    await log.append_async(make_trace(description="event 2"))

    assert len(received) == 2
    assert received[0].trace.description == "event 1"
    assert received[1].trace.description == "event 2"


@pytest.mark.asyncio
async def test_sync_append_does_not_notify():
    """Sync append() should NOT notify subscribers."""
    log = ImmutableTraceLog()
    received: list[HashedTrace] = []

    async def callback(hashed: HashedTrace) -> None:
        received.append(hashed)

    log.subscribe(callback)
    log.append(make_trace(description="sync event"))

    assert len(received) == 0
    assert len(log) == 1


@pytest.mark.asyncio
async def test_multiple_subscribers():
    """Multiple subscribers should all receive events."""
    log = ImmutableTraceLog()
    received_a: list[HashedTrace] = []
    received_b: list[HashedTrace] = []

    async def callback_a(hashed: HashedTrace) -> None:
        received_a.append(hashed)

    async def callback_b(hashed: HashedTrace) -> None:
        received_b.append(hashed)

    log.subscribe(callback_a)
    log.subscribe(callback_b)
    await log.append_async(make_trace(description="shared event"))

    assert len(received_a) == 1
    assert len(received_b) == 1
    assert received_a[0].trace.description == "shared event"
    assert received_b[0].trace.description == "shared event"


@pytest.mark.asyncio
async def test_unsubscribe_stops_notifications():
    """After unsubscribe, callback should not receive new events."""
    log = ImmutableTraceLog()
    received: list[HashedTrace] = []

    async def callback(hashed: HashedTrace) -> None:
        received.append(hashed)

    log.subscribe(callback)
    await log.append_async(make_trace(description="before unsub"))
    assert len(received) == 1

    log.unsubscribe(callback)
    await log.append_async(make_trace(description="after unsub"))
    assert len(received) == 1  # no new events


@pytest.mark.asyncio
async def test_subscriber_error_does_not_break_log():
    """A failing subscriber should not prevent other subscribers or trace logging."""
    log = ImmutableTraceLog()
    received: list[HashedTrace] = []

    async def bad_callback(hashed: HashedTrace) -> None:
        raise RuntimeError("subscriber crash")

    async def good_callback(hashed: HashedTrace) -> None:
        received.append(hashed)

    log.subscribe(bad_callback)
    log.subscribe(good_callback)
    await log.append_async(make_trace(description="event"))

    assert len(received) == 1  # good callback still works
    assert len(log) == 1  # event still logged


@pytest.mark.asyncio
async def test_subscriber_receives_hash_chain():
    """Subscriber should receive events with correct hash chaining."""
    log = ImmutableTraceLog()
    received: list[HashedTrace] = []

    async def callback(hashed: HashedTrace) -> None:
        received.append(hashed)

    log.subscribe(callback)
    await log.append_async(make_trace(description="first"))
    await log.append_async(make_trace(description="second"))

    assert received[0].sequence == 0
    assert received[0].previous_hash == ImmutableTraceLog.GENESIS_HASH
    assert received[1].sequence == 1
    assert received[1].previous_hash == received[0].hash


@pytest.mark.asyncio
async def test_subscriber_receives_trace_fields():
    """Subscriber should receive full trace data including all fields."""
    log = ImmutableTraceLog()
    received: list[HashedTrace] = []

    async def callback(hashed: HashedTrace) -> None:
        received.append(hashed)

    log.subscribe(callback)
    await log.append_async(make_trace(
        intent_id="intent-123",
        task_id="task-456",
        event_type="EXECUTION_START",
        description="Starting execution",
        details={"wave": 1, "tasks": ["a", "b"]},
    ))

    assert len(received) == 1
    t = received[0].trace
    assert t.intent_id == "intent-123"
    assert t.task_id == "task-456"
    assert t.event_type == "EXECUTION_START"
    assert t.details["wave"] == 1


@pytest.mark.asyncio
async def test_integrity_preserved_with_async():
    """Hash chain integrity should be preserved when using append_async."""
    log = ImmutableTraceLog()
    log.subscribe(lambda h: asyncio.sleep(0))  # no-op subscriber

    for i in range(5):
        await log.append_async(make_trace(description=f"event {i}"))

    valid, msg = log.verify_integrity()
    assert valid, f"Integrity check failed: {msg}"
    assert len(log) == 5


@pytest.mark.asyncio
async def test_broadcast_trace_data_shape():
    """Verify the shape of data a WS broadcast callback would receive."""
    log = ImmutableTraceLog()
    broadcast_messages: list[dict] = []

    async def ws_broadcast(hashed: HashedTrace) -> None:
        t = hashed.trace
        broadcast_messages.append({
            "type": "trace",
            "intent_id": t.intent_id,
            "data": {
                "id": t.id,
                "timestamp": t.timestamp.isoformat(),
                "intent_id": t.intent_id,
                "task_id": t.task_id,
                "event_type": t.event_type,
                "description": t.description,
                "details": t.details or {},
                "risk_level": t.risk_level.value if t.risk_level else None,
                "l0_passed": t.l0_passed,
            },
        })

    log.subscribe(ws_broadcast)
    await log.append_async(make_trace(
        intent_id="ws-test",
        event_type="INTENT_RECEIVED",
        description="WS test intent",
    ))

    assert len(broadcast_messages) == 1
    msg = broadcast_messages[0]
    assert msg["type"] == "trace"
    assert msg["intent_id"] == "ws-test"
    assert msg["data"]["event_type"] == "INTENT_RECEIVED"
    assert msg["data"]["description"] == "WS test intent"
    assert isinstance(msg["data"]["timestamp"], str)
