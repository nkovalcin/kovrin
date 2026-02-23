"""Tests for LATTICE core data models."""

import pytest

from kovrin.core.models import (
    ExecutionResult,
    ProofObligation,
    RiskLevel,
    RoutingAction,
    RoutingDecision,
    SpeculationTier,
    SubTask,
    TaskStatus,
    Trace,
)


class TestRiskLevel:
    def test_all_levels(self):
        assert RiskLevel.LOW.value == "LOW"
        assert RiskLevel.MEDIUM.value == "MEDIUM"
        assert RiskLevel.HIGH.value == "HIGH"
        assert RiskLevel.CRITICAL.value == "CRITICAL"

    def test_from_string(self):
        assert RiskLevel("LOW") == RiskLevel.LOW


class TestTaskStatus:
    def test_all_statuses(self):
        statuses = [s.value for s in TaskStatus]
        assert "PENDING" in statuses
        assert "COMPLETED" in statuses
        assert "REJECTED_BY_L0" in statuses
        assert "SKIPPED" in statuses


class TestSubTask:
    def test_default_values(self):
        task = SubTask(description="Test task")
        assert task.id.startswith("task-")
        assert task.risk_level == RiskLevel.LOW
        assert task.status == TaskStatus.PENDING
        assert task.speculation_tier == SpeculationTier.FREE
        assert task.output is None
        assert task.dependencies == []
        assert task.proof_obligations == []

    def test_custom_values(self):
        task = SubTask(
            id="custom-id",
            description="Custom task",
            risk_level=RiskLevel.HIGH,
            speculation_tier=SpeculationTier.NONE,
            dependencies=["dep-1", "dep-2"],
        )
        assert task.id == "custom-id"
        assert task.risk_level == RiskLevel.HIGH
        assert len(task.dependencies) == 2

    def test_serialization(self):
        task = SubTask(description="Serializable task", risk_level=RiskLevel.MEDIUM)
        data = task.model_dump()
        assert data["description"] == "Serializable task"
        assert data["risk_level"] == "MEDIUM"

        # Round-trip
        restored = SubTask.model_validate(data)
        assert restored.description == task.description
        assert restored.risk_level == task.risk_level


class TestProofObligation:
    def test_creation(self):
        po = ProofObligation(
            axiom_id=1,
            axiom_name="Human Agency",
            description="No removal of override",
            passed=True,
            evidence="Task is read-only analysis",
        )
        assert po.passed is True
        assert po.axiom_id == 1


class TestTrace:
    def test_default_timestamp(self):
        trace = Trace(event_type="TEST", description="Test event")
        assert trace.timestamp is not None
        assert trace.id.startswith("tr-")

    def test_full_trace(self):
        trace = Trace(
            intent_id="i-1",
            task_id="t-1",
            event_type="EXECUTION",
            description="Executed task",
            details={"output_length": 500},
            risk_level=RiskLevel.LOW,
            l0_passed=True,
        )
        assert trace.l0_passed is True
        assert trace.details["output_length"] == 500


class TestRoutingDecision:
    def test_auto_execute(self):
        rd = RoutingDecision(
            task_id="t-1",
            action=RoutingAction.AUTO_EXECUTE,
            risk_level=RiskLevel.LOW,
            speculation_tier=SpeculationTier.FREE,
            reason="Safe for auto-execution",
        )
        assert rd.action == RoutingAction.AUTO_EXECUTE


class TestExecutionResult:
    def test_empty_result(self):
        result = ExecutionResult(intent_id="test")
        assert result.success is True
        assert result.output == ""
        assert result.sub_tasks == []

    def test_failed_result(self):
        result = ExecutionResult(
            intent_id="test",
            success=False,
            output="All tasks rejected",
            rejected_tasks=[SubTask(description="Bad task")],
        )
        assert not result.success
        assert len(result.rejected_tasks) == 1
