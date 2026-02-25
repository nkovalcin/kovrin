"""Tests for PersistentTraceLog (ImmutableTraceLog + EventStoreDB)."""

import json
from unittest.mock import MagicMock, call, patch

import pytest

from kovrin.audit.persistent_trace_log import PersistentTraceLog
from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import Trace


def _make_trace(event_type: str = "TEST_EVENT", description: str = "test") -> Trace:
    return Trace(
        intent_id="intent-1",
        event_type=event_type,
        description=description,
    )


class TestConstruction:
    def test_inherits_immutable_trace_log(self):
        es = MagicMock()
        log = PersistentTraceLog(es, intent_id="abc")
        assert isinstance(log, ImmutableTraceLog)
        assert log._stream_name == "pipeline-abc"
        assert log._intent_id == "abc"

    def test_default_intent_id(self):
        es = MagicMock()
        log = PersistentTraceLog(es)
        assert log._stream_name == "pipeline-unknown"


class TestAppend:
    def test_appends_to_memory_and_esdb(self):
        es = MagicMock()
        log = PersistentTraceLog(es, intent_id="test-1")

        trace = _make_trace()
        hashed = log.append(trace)

        # In-memory chain works
        assert len(log) == 1
        assert hashed.sequence == 0
        assert hashed.hash != ""

        # EventStoreDB was called
        es.append.assert_called_once()
        call_kwargs = es.append.call_args
        assert call_kwargs.kwargs["stream_name"] == "pipeline-test-1"
        assert call_kwargs.kwargs["event_type"] == "TraceAppended"
        assert call_kwargs.kwargs["data"]["hash"] == hashed.hash

    def test_esdb_failure_does_not_break_chain(self):
        es = MagicMock()
        es.append.side_effect = ConnectionError("ESDB down")

        log = PersistentTraceLog(es, intent_id="test-2")
        trace = _make_trace()

        # Should not raise
        hashed = log.append(trace)
        assert len(log) == 1
        assert hashed.hash != ""

    def test_multiple_appends_chain_correctly(self):
        es = MagicMock()
        log = PersistentTraceLog(es, intent_id="test-3")

        h1 = log.append(_make_trace("EVENT_1", "first"))
        h2 = log.append(_make_trace("EVENT_2", "second"))

        assert h2.previous_hash == h1.hash
        assert len(log) == 2
        assert es.append.call_count == 2

    def test_verify_integrity_works(self):
        es = MagicMock()
        log = PersistentTraceLog(es, intent_id="test-4")

        log.append(_make_trace("A"))
        log.append(_make_trace("B"))
        log.append(_make_trace("C"))

        valid, msg = log.verify_integrity()
        assert valid is True
        assert "3 events verified" in msg


class TestAppendAsync:
    @pytest.mark.asyncio
    async def test_async_append_persists(self):
        es = MagicMock()
        log = PersistentTraceLog(es, intent_id="async-1")

        hashed = await log.append_async(_make_trace())
        assert len(log) == 1
        es.append.assert_called_once()

    @pytest.mark.asyncio
    async def test_async_notifies_subscribers(self):
        from unittest.mock import AsyncMock

        es = MagicMock()
        log = PersistentTraceLog(es, intent_id="async-2")

        cb = AsyncMock()
        log.subscribe(cb)

        await log.append_async(_make_trace())
        cb.assert_called_once()


class TestVerifyFromStore:
    def test_empty_store(self):
        es = MagicMock()
        es.read_stream.return_value = []

        valid, msg = PersistentTraceLog.verify_from_store(es, "empty")
        assert valid is True
        assert "No events" in msg

    def test_valid_chain_from_store(self):
        """Build a real chain, persist mock data, verify from store."""
        es_mock = MagicMock()
        log = PersistentTraceLog(es_mock, intent_id="verify-1")

        # Append 3 events to get real hashes
        traces = [_make_trace(f"E{i}", f"desc {i}") for i in range(3)]
        hashed_events = [log.append(t) for t in traces]

        # Build stored events matching what ESDB would return
        from kovrin.storage.eventstore import StoredEvent

        stored = []
        for h in hashed_events:
            stored.append(StoredEvent(
                stream_name="pipeline-verify-1",
                event_type="TraceAppended",
                data={
                    "sequence": h.sequence,
                    "hash": h.hash,
                    "previous_hash": h.previous_hash,
                    "trace_id": h.trace.id,
                    "intent_id": h.trace.intent_id,
                    "task_id": h.trace.task_id,
                    "event_type": h.trace.event_type,
                    "description": h.trace.description,
                    "details": h.trace.details,
                    "timestamp": h.trace.timestamp.isoformat(),
                },
            ))

        es_read = MagicMock()
        es_read.read_stream.return_value = stored

        valid, msg = PersistentTraceLog.verify_from_store(es_read, "verify-1")
        assert valid is True
        assert "3 events verified" in msg

    def test_tampered_chain_from_store(self):
        from kovrin.storage.eventstore import StoredEvent

        stored = [
            StoredEvent(
                stream_name="pipeline-tampered",
                event_type="TraceAppended",
                data={
                    "sequence": 0,
                    "hash": "fakehash",
                    "previous_hash": "0" * 64,
                    "trace_id": "t1",
                    "intent_id": "i1",
                    "task_id": "",
                    "event_type": "TEST",
                    "description": "tampered",
                    "details": None,
                    "timestamp": "2026-01-01T00:00:00",
                },
            )
        ]

        es = MagicMock()
        es.read_stream.return_value = stored

        valid, msg = PersistentTraceLog.verify_from_store(es, "tampered")
        assert valid is False
        assert "Tampered" in msg

    def test_broken_chain_link(self):
        from kovrin.storage.eventstore import StoredEvent

        stored = [
            StoredEvent(
                stream_name="pipeline-broken",
                event_type="TraceAppended",
                data={
                    "sequence": 0,
                    "hash": "abc",
                    "previous_hash": "wrong_genesis",  # Should be 0*64
                    "trace_id": "t1",
                    "intent_id": "i1",
                    "task_id": "",
                    "event_type": "TEST",
                    "description": "broken",
                    "details": None,
                    "timestamp": "2026-01-01T00:00:00",
                },
            )
        ]

        es = MagicMock()
        es.read_stream.return_value = stored

        valid, msg = PersistentTraceLog.verify_from_store(es, "broken")
        assert valid is False
        assert "Chain broken" in msg
