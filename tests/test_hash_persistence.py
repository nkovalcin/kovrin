"""Tests for LATTICE Phase 5 — Hash Chain Persistence and Autonomy Storage."""

import pytest

from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import (
    AutonomyProfile,
    AutonomySettings,
    ExecutionResult,
    RiskLevel,
    SubTask,
    TaskStatus,
    Trace,
)
from kovrin.storage.repository import PipelineRepository


class TestAutonomyPersistence:
    def test_save_and_load_autonomy(self):
        repo = PipelineRepository(":memory:")
        settings = AutonomySettings(
            profile=AutonomyProfile.CAUTIOUS,
            override_matrix={"HIGH:FREE": "HUMAN_APPROVAL", "LOW:NONE": "AUTO_EXECUTE"},
        )
        repo.save_autonomy_settings(settings)

        loaded = repo.get_autonomy_settings()
        assert loaded.profile == AutonomyProfile.CAUTIOUS
        assert loaded.override_matrix == {"HIGH:FREE": "HUMAN_APPROVAL", "LOW:NONE": "AUTO_EXECUTE"}
        repo.close()

    def test_load_default_when_empty(self):
        repo = PipelineRepository(":memory:")
        loaded = repo.get_autonomy_settings()
        assert loaded.profile == AutonomyProfile.DEFAULT
        assert loaded.override_matrix == {}
        repo.close()

    def test_upsert_overwrites(self):
        repo = PipelineRepository(":memory:")
        repo.save_autonomy_settings(AutonomySettings(profile=AutonomyProfile.CAUTIOUS))
        repo.save_autonomy_settings(AutonomySettings(profile=AutonomyProfile.AGGRESSIVE))

        loaded = repo.get_autonomy_settings()
        assert loaded.profile == AutonomyProfile.AGGRESSIVE
        repo.close()


class TestHashChainPersistence:
    def _make_result_with_traces(self, intent_id: str = "test-intent") -> tuple[ExecutionResult, list[dict]]:
        """Create a result with traces and matching hash data."""
        log = ImmutableTraceLog()
        traces = []
        hash_data = []

        for i in range(3):
            trace = Trace(
                intent_id=intent_id,
                task_id=f"task-{i}",
                event_type=f"EVENT_{i}",
                description=f"Event {i}",
                risk_level=RiskLevel.LOW if i == 0 else RiskLevel.MEDIUM,
            )
            hashed = log.append(trace)
            traces.append(trace)
            hash_data.append({
                "trace_id": trace.id,
                "hash": hashed.hash,
                "previous_hash": hashed.previous_hash,
                "sequence": hashed.sequence,
            })

        result = ExecutionResult(
            intent_id=intent_id,
            output="Test output",
            success=True,
            traces=traces,
        )
        return result, hash_data

    def test_save_and_retrieve_hashes(self):
        repo = PipelineRepository(":memory:")
        result, hash_data = self._make_result_with_traces("hash-test")

        repo.save_result(result, intent="Test", hashed_traces=hash_data)

        rows = repo.get_traces_with_hashes("hash-test")
        assert len(rows) == 3

        # First event should link to GENESIS
        genesis = "0" * 64
        assert rows[0]["previous_hash"] == genesis
        assert rows[0]["hash"] != ""
        assert rows[0]["sequence"] == 0

        # Chain should link
        assert rows[1]["previous_hash"] == rows[0]["hash"]
        assert rows[2]["previous_hash"] == rows[1]["hash"]
        repo.close()

    def test_backward_compat_without_hashes(self):
        """Saving without hashed_traces should still work (empty hash fields)."""
        repo = PipelineRepository(":memory:")
        result = ExecutionResult(
            intent_id="no-hash",
            output="Test",
            success=True,
            traces=[
                Trace(intent_id="no-hash", event_type="TEST"),
            ],
        )

        repo.save_result(result, intent="Test")

        rows = repo.get_traces_with_hashes("no-hash")
        assert len(rows) == 1
        assert rows[0]["hash"] == ""
        assert rows[0]["previous_hash"] == ""
        assert rows[0]["sequence"] == 0
        repo.close()

    def test_chain_integrity_from_stored_data(self):
        """Verify that stored hash chain is valid."""
        repo = PipelineRepository(":memory:")
        result, hash_data = self._make_result_with_traces("chain-test")
        repo.save_result(result, intent="Test", hashed_traces=hash_data)

        rows = repo.get_traces_with_hashes("chain-test")

        # Verify chain
        for i in range(1, len(rows)):
            assert rows[i]["previous_hash"] == rows[i - 1]["hash"], \
                f"Chain broken at frame {i}"
        repo.close()

    def test_get_traces_with_hashes_returns_all_fields(self):
        repo = PipelineRepository(":memory:")
        result, hash_data = self._make_result_with_traces("fields-test")
        repo.save_result(result, intent="Test", hashed_traces=hash_data)

        rows = repo.get_traces_with_hashes("fields-test")
        row = rows[0]

        assert "trace_id" in row
        assert "intent_id" in row
        assert "task_id" in row
        assert "event_type" in row
        assert "description" in row
        assert "details" in row
        assert "risk_level" in row
        assert "timestamp" in row
        assert "hash" in row
        assert "previous_hash" in row
        assert "sequence" in row
        repo.close()
