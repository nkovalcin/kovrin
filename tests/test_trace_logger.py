"""Tests for LATTICE Immutable Trace Logger."""

import json
import tempfile
from pathlib import Path

import pydantic
import pytest

from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import RiskLevel, Trace


class TestImmutableTraceLog:
    def test_empty_log(self):
        log = ImmutableTraceLog()
        assert len(log) == 0
        valid, msg = log.verify_integrity()
        assert valid is True

    def test_append_single(self, sample_trace):
        log = ImmutableTraceLog()
        hashed = log.append(sample_trace)
        assert len(log) == 1
        assert hashed.sequence == 0
        assert hashed.previous_hash == ImmutableTraceLog.GENESIS_HASH

    def test_append_multiple_chain(self):
        log = ImmutableTraceLog()
        t1 = Trace(event_type="E1", description="Event 1")
        t2 = Trace(event_type="E2", description="Event 2")
        t3 = Trace(event_type="E3", description="Event 3")

        h1 = log.append(t1)
        h2 = log.append(t2)
        h3 = log.append(t3)

        assert h2.previous_hash == h1.hash
        assert h3.previous_hash == h2.hash
        assert len(log) == 3

    def test_verify_integrity_valid(self):
        log = ImmutableTraceLog()
        for i in range(10):
            log.append(Trace(event_type="TEST", description=f"Event {i}"))

        valid, msg = log.verify_integrity()
        assert valid is True
        assert "10 events verified" in msg

    def test_verify_integrity_tampered_hash(self):
        log = ImmutableTraceLog()
        log.append(Trace(event_type="E1", description="Event 1"))
        log.append(Trace(event_type="E2", description="Event 2"))

        # Tamper with the hash
        log._events[0].hash = "tampered_hash_value"

        valid, msg = log.verify_integrity()
        assert valid is False
        assert "Tampered" in msg or "Chain broken" in msg

    def test_verify_integrity_tampered_content(self):
        log = ImmutableTraceLog()
        log.append(Trace(event_type="E1", description="Event 1"))
        log.append(Trace(event_type="E2", description="Event 2"))

        # Trace is frozen (immutable) — direct modification is blocked at Pydantic level
        with pytest.raises(pydantic.ValidationError, match="frozen"):
            log._events[0].trace.description = "MODIFIED"

    def test_head_hash_updates(self):
        log = ImmutableTraceLog()
        assert log.head_hash == ImmutableTraceLog.GENESIS_HASH

        h1 = log.append(Trace(event_type="E1", description="Event 1"))
        assert log.head_hash == h1.hash

    def test_get_events_filter_by_intent(self):
        log = ImmutableTraceLog()
        log.append(Trace(intent_id="A", event_type="E1", description="E1"))
        log.append(Trace(intent_id="B", event_type="E2", description="E2"))
        log.append(Trace(intent_id="A", event_type="E3", description="E3"))

        results = log.get_events(intent_id="A")
        assert len(results) == 2

    def test_get_events_filter_by_type(self):
        log = ImmutableTraceLog()
        log.append(Trace(event_type="L0_CHECK", description="E1"))
        log.append(Trace(event_type="EXECUTION", description="E2"))
        log.append(Trace(event_type="L0_CHECK", description="E3"))

        results = log.get_events(event_type="L0_CHECK")
        assert len(results) == 2

    def test_export_json(self):
        log = ImmutableTraceLog()
        log.append(
            Trace(
                intent_id="test",
                event_type="E1",
                description="Export test",
                risk_level=RiskLevel.LOW,
                l0_passed=True,
            )
        )

        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
            path = f.name

        log.export_json(path)

        data = json.loads(Path(path).read_text())
        assert data["total_events"] == 1
        assert data["events"][0]["trace"]["event_type"] == "E1"
        assert data["events"][0]["trace"]["l0_passed"] is True

        Path(path).unlink()

    def test_append_is_append_only(self):
        """Events cannot be removed from the log."""
        log = ImmutableTraceLog()
        log.append(Trace(event_type="E1", description="Event 1"))
        assert len(log) == 1
        # No delete method should exist
        assert not hasattr(log, "delete")
        assert not hasattr(log, "remove")
        assert not hasattr(log, "pop")
