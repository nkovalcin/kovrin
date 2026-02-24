"""
Tests for Human-in-the-loop Approval flow.

Verifies:
- Async approval callback flow (approve / reject / timeout)
- CLI fallback when no callback
- ApprovalRequest model
- API endpoint resolve
"""

import asyncio
from unittest.mock import MagicMock, patch

import pytest

from kovrin.core.models import (
    ApprovalRequest,
    ApprovalStatus,
    ProofObligation,
    RiskLevel,
    RoutingAction,
    RoutingDecision,
    SpeculationTier,
    SubTask,
)
from kovrin.engine.risk_router import RiskRouter

# ─── Helpers ────────────────────────────────────────────────


def make_subtask(**kwargs) -> SubTask:
    defaults = {
        "description": "Delete user data from production database",
        "risk_level": RiskLevel.HIGH,
        "speculation_tier": SpeculationTier.NONE,
        "parent_intent_id": "test-intent-123",
    }
    defaults.update(kwargs)
    return SubTask(**defaults)


def make_decision(subtask: SubTask) -> RoutingDecision:
    return RoutingDecision(
        task_id=subtask.id,
        action=RoutingAction.HUMAN_APPROVAL,
        risk_level=subtask.risk_level,
        speculation_tier=subtask.speculation_tier,
        reason="Risk=HIGH, Tier=NONE — requires human approval",
    )


# ─── ApprovalRequest Model ─────────────────────────────────


class TestApprovalRequest:
    def test_create_approval_request(self):
        req = ApprovalRequest(
            intent_id="intent-1",
            task_id="task-1",
            description="Delete records",
            risk_level=RiskLevel.HIGH,
            speculation_tier=SpeculationTier.NONE,
            reason="High risk task",
        )
        assert req.intent_id == "intent-1"
        assert req.task_id == "task-1"
        assert req.status == ApprovalStatus.PENDING
        assert req.risk_level == RiskLevel.HIGH

    def test_approval_request_with_obligations(self):
        po = ProofObligation(
            axiom_id=1,
            axiom_name="A1 — Human Primacy",
            description="Test",
            passed=True,
            evidence="Safe action",
        )
        req = ApprovalRequest(
            intent_id="intent-1",
            task_id="task-1",
            description="Test",
            risk_level=RiskLevel.MEDIUM,
            speculation_tier=SpeculationTier.GUARDED,
            proof_obligations=[po],
        )
        assert len(req.proof_obligations) == 1
        assert req.proof_obligations[0].axiom_name == "A1 — Human Primacy"

    def test_approval_status_values(self):
        assert ApprovalStatus.PENDING == "PENDING"
        assert ApprovalStatus.APPROVED == "APPROVED"
        assert ApprovalStatus.REJECTED == "REJECTED"
        assert ApprovalStatus.TIMEOUT == "TIMEOUT"


# ─── Async Approval Callback ──────────────────────────────


class TestAsyncApproval:
    @pytest.mark.asyncio
    async def test_approve_via_callback(self):
        """Approval callback returns True -> task approved."""
        router = RiskRouter()
        subtask = make_subtask()
        decision = make_decision(subtask)

        async def callback(req: ApprovalRequest):
            future = asyncio.get_event_loop().create_future()
            future.set_result(True)
            return future

        result = await router.request_human_approval(subtask, decision, approval_callback=callback)
        assert result is True

    @pytest.mark.asyncio
    async def test_reject_via_callback(self):
        """Approval callback returns False -> task rejected."""
        router = RiskRouter()
        subtask = make_subtask()
        decision = make_decision(subtask)

        async def callback(req: ApprovalRequest):
            future = asyncio.get_event_loop().create_future()
            future.set_result(False)
            return future

        result = await router.request_human_approval(subtask, decision, approval_callback=callback)
        assert result is False

    @pytest.mark.asyncio
    async def test_timeout_rejects(self):
        """If approval times out, task is rejected."""
        router = RiskRouter()
        subtask = make_subtask()
        decision = make_decision(subtask)

        async def callback(req: ApprovalRequest):
            # Return a future that never resolves
            future = asyncio.get_event_loop().create_future()
            return future

        result = await router.request_human_approval(
            subtask, decision, approval_callback=callback, timeout=0.1
        )
        assert result is False

    @pytest.mark.asyncio
    async def test_callback_receives_correct_request(self):
        """Callback receives ApprovalRequest with correct fields."""
        router = RiskRouter()
        subtask = make_subtask(
            description="Critical operation",
            risk_level=RiskLevel.CRITICAL,
        )
        decision = make_decision(subtask)
        received_requests: list[ApprovalRequest] = []

        async def callback(req: ApprovalRequest):
            received_requests.append(req)
            future = asyncio.get_event_loop().create_future()
            future.set_result(True)
            return future

        await router.request_human_approval(subtask, decision, approval_callback=callback)

        assert len(received_requests) == 1
        req = received_requests[0]
        assert req.task_id == subtask.id
        assert req.intent_id == subtask.parent_intent_id
        assert req.description == "Critical operation"
        assert req.risk_level == RiskLevel.CRITICAL

    @pytest.mark.asyncio
    async def test_delayed_approval(self):
        """Approval that comes after a short delay should still work."""
        router = RiskRouter()
        subtask = make_subtask()
        decision = make_decision(subtask)

        async def callback(req: ApprovalRequest):
            future = asyncio.get_event_loop().create_future()

            # Simulate delayed approval
            async def resolve_later():
                await asyncio.sleep(0.05)
                future.set_result(True)

            asyncio.create_task(resolve_later())
            return future

        result = await router.request_human_approval(
            subtask, decision, approval_callback=callback, timeout=1.0
        )
        assert result is True


# ─── CLI Fallback ──────────────────────────────────────────


class TestCLIFallback:
    @pytest.mark.asyncio
    async def test_cli_approve(self):
        """CLI mode: 'y' input approves."""
        router = RiskRouter()
        subtask = make_subtask()
        decision = make_decision(subtask)

        with patch("builtins.input", return_value="y"):
            result = await router.request_human_approval(subtask, decision)
        assert result is True

    @pytest.mark.asyncio
    async def test_cli_reject(self):
        """CLI mode: 'n' input rejects."""
        router = RiskRouter()
        subtask = make_subtask()
        decision = make_decision(subtask)

        with patch("builtins.input", return_value="n"):
            result = await router.request_human_approval(subtask, decision)
        assert result is False

    @pytest.mark.asyncio
    async def test_cli_eof_rejects(self):
        """CLI mode: EOFError (non-interactive) rejects."""
        router = RiskRouter()
        subtask = make_subtask()
        decision = make_decision(subtask)

        with patch("builtins.input", side_effect=EOFError):
            result = await router.request_human_approval(subtask, decision)
        assert result is False

    @pytest.mark.asyncio
    async def test_cli_empty_input_rejects(self):
        """CLI mode: empty input defaults to reject."""
        router = RiskRouter()
        subtask = make_subtask()
        decision = make_decision(subtask)

        with patch("builtins.input", return_value=""):
            result = await router.request_human_approval(subtask, decision)
        assert result is False


# ─── Executor Integration ──────────────────────────────────


class TestExecutorApproval:
    def test_executor_accepts_callback(self):
        """TaskExecutor should accept approval_callback parameter."""
        from kovrin.engine.executor import TaskExecutor

        mock_callback = MagicMock()
        executor = TaskExecutor(approval_callback=mock_callback)
        assert executor._approval_callback is mock_callback

    def test_executor_default_no_callback(self):
        """TaskExecutor without callback defaults to None."""
        from kovrin.engine.executor import TaskExecutor

        executor = TaskExecutor()
        assert executor._approval_callback is None


# ─── API Approval Manager ─────────────────────────────────


class TestApprovalManager:
    @pytest.mark.asyncio
    async def test_resolve_approval_approve(self):
        """PipelineManager.resolve_approval should resolve Future with True."""
        from kovrin.api.server import PipelineManager

        mgr = PipelineManager()
        loop = asyncio.get_event_loop()
        future = loop.create_future()

        mgr._pending_approvals["intent-1:task-1"] = future
        mgr._approval_requests["intent-1:task-1"] = ApprovalRequest(
            intent_id="intent-1",
            task_id="task-1",
            description="test",
            risk_level=RiskLevel.HIGH,
            speculation_tier=SpeculationTier.NONE,
        )

        resolved = mgr.resolve_approval("intent-1", "task-1", True)
        assert resolved is True
        assert await future is True
        assert "intent-1:task-1" not in mgr._pending_approvals

    @pytest.mark.asyncio
    async def test_resolve_approval_reject(self):
        """PipelineManager.resolve_approval should resolve Future with False."""
        from kovrin.api.server import PipelineManager

        mgr = PipelineManager()
        loop = asyncio.get_event_loop()
        future = loop.create_future()

        mgr._pending_approvals["intent-1:task-1"] = future
        mgr._approval_requests["intent-1:task-1"] = ApprovalRequest(
            intent_id="intent-1",
            task_id="task-1",
            description="test",
            risk_level=RiskLevel.HIGH,
            speculation_tier=SpeculationTier.NONE,
        )

        resolved = mgr.resolve_approval("intent-1", "task-1", False)
        assert resolved is True
        assert await future is False

    @pytest.mark.asyncio
    async def test_resolve_nonexistent(self):
        """Resolving a non-existent approval returns False."""
        from kovrin.api.server import PipelineManager

        mgr = PipelineManager()
        resolved = mgr.resolve_approval("nope", "nope", True)
        assert resolved is False

    @pytest.mark.asyncio
    async def test_pending_approvals_list(self):
        """pending_approvals property should return list of pending requests."""
        from kovrin.api.server import PipelineManager

        mgr = PipelineManager()
        mgr._approval_requests["intent-1:task-1"] = ApprovalRequest(
            intent_id="intent-1",
            task_id="task-1",
            description="Delete data",
            risk_level=RiskLevel.HIGH,
            speculation_tier=SpeculationTier.NONE,
            reason="High risk",
        )

        approvals = mgr.pending_approvals
        assert len(approvals) == 1
        assert approvals[0]["task_id"] == "task-1"
        assert approvals[0]["description"] == "Delete data"
