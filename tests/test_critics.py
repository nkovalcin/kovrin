"""Tests for Kovrin LLM-Modulo Critics.

Tests SafetyCritic, FeasibilityCritic, PolicyCritic, and CriticPipeline
using mocked Claude API responses.
"""

import json
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin.core.constitutional import ConstitutionalCore
from kovrin.core.models import ProofObligation, RiskLevel, SpeculationTier, SubTask
from kovrin.safety.critics import (
    CriticPipeline,
    FeasibilityCritic,
    PolicyCritic,
    SafetyCritic,
)


def _make_subtask(
    desc: str = "Test task",
    risk: RiskLevel = RiskLevel.LOW,
    tier: SpeculationTier = SpeculationTier.FREE,
) -> SubTask:
    return SubTask(
        description=desc,
        risk_level=risk,
        speculation_tier=tier,
        parent_intent_id="test-intent",
    )


def _mock_claude_response(text: str) -> MagicMock:
    """Create a mock Anthropic message response."""
    msg = MagicMock()
    content_block = MagicMock()
    content_block.text = text
    msg.content = [content_block]
    return msg


# ─── SafetyCritic ─────────────────────────────────────────


class TestSafetyCritic:
    """SafetyCritic delegates to ConstitutionalCore."""

    @pytest.mark.asyncio
    async def test_delegates_to_constitutional_core(self):
        """SafetyCritic.evaluate should call ConstitutionalCore.check."""
        core = AsyncMock(spec=ConstitutionalCore)
        obligations = [
            ProofObligation(
                axiom_id=1,
                axiom_name="Human Agency",
                description="test",
                passed=True,
                evidence="ok",
            )
        ]
        core.check = AsyncMock(return_value=obligations)

        critic = SafetyCritic(core)
        result = await critic.evaluate(_make_subtask(), "test context")

        core.check.assert_called_once()
        assert result == obligations

    def test_passed_all_true(self):
        obligations = [
            ProofObligation(axiom_id=i, axiom_name=f"A{i}", description="", passed=True, evidence="")
            for i in range(5)
        ]
        assert SafetyCritic.passed(obligations) is True

    def test_passed_one_false(self):
        obligations = [
            ProofObligation(axiom_id=1, axiom_name="A1", description="", passed=True, evidence=""),
            ProofObligation(axiom_id=2, axiom_name="A2", description="", passed=False, evidence="fail"),
        ]
        assert SafetyCritic.passed(obligations) is False


# ─── FeasibilityCritic ─────────────────────────────────────


class TestFeasibilityCritic:
    """FeasibilityCritic checks task feasibility via Claude API."""

    @pytest.mark.asyncio
    async def test_feasible_task(self):
        client = AsyncMock()
        client.messages.create = AsyncMock(
            return_value=_mock_claude_response(json.dumps({"feasible": True, "reason": "Task is doable"}))
        )

        critic = FeasibilityCritic(client=client, available_tools=["web_search"])
        result = await critic.evaluate(_make_subtask("Search for AI news"))

        assert result.passed is True
        assert "doable" in result.evidence

    @pytest.mark.asyncio
    async def test_infeasible_task(self):
        client = AsyncMock()
        client.messages.create = AsyncMock(
            return_value=_mock_claude_response(
                json.dumps({"feasible": False, "reason": "Requires physical action"})
            )
        )

        critic = FeasibilityCritic(client=client)
        result = await critic.evaluate(_make_subtask("Move the server rack"))

        assert result.passed is False

    @pytest.mark.asyncio
    async def test_parse_error_returns_fail_safe(self):
        client = AsyncMock()
        client.messages.create = AsyncMock(
            return_value=_mock_claude_response("invalid json response")
        )

        critic = FeasibilityCritic(client=client)
        result = await critic.evaluate(_make_subtask())

        assert result.passed is False
        assert "fail-safe" in result.evidence

    @pytest.mark.asyncio
    async def test_tools_included_in_prompt(self):
        client = AsyncMock()
        client.messages.create = AsyncMock(
            return_value=_mock_claude_response(json.dumps({"feasible": True, "reason": "ok"}))
        )

        critic = FeasibilityCritic(
            client=client, available_tools=["web_search", "calculator"]
        )
        await critic.evaluate(_make_subtask())

        # Verify the prompt includes tool names
        call_args = client.messages.create.call_args
        prompt = call_args.kwargs["messages"][0]["content"]
        assert "web_search" in prompt
        assert "calculator" in prompt


# ─── PolicyCritic ──────────────────────────────────────────


class TestPolicyCritic:
    """PolicyCritic validates organizational constraints."""

    @pytest.mark.asyncio
    async def test_no_constraints_auto_pass(self):
        client = AsyncMock()
        critic = PolicyCritic(client=client)
        result = await critic.evaluate(_make_subtask(), constraints=[])

        assert result.passed is True
        assert "auto-pass" in result.evidence
        # Should NOT call the API
        client.messages.create.assert_not_called()

    @pytest.mark.asyncio
    async def test_compliant_task(self):
        client = AsyncMock()
        client.messages.create = AsyncMock(
            return_value=_mock_claude_response(
                json.dumps({"compliant": True, "violated_constraints": [], "reason": "All good"})
            )
        )

        critic = PolicyCritic(client=client)
        result = await critic.evaluate(
            _make_subtask("Analyze costs"),
            constraints=["Focus on operational costs only"],
        )

        assert result.passed is True

    @pytest.mark.asyncio
    async def test_non_compliant_task(self):
        client = AsyncMock()
        client.messages.create = AsyncMock(
            return_value=_mock_claude_response(
                json.dumps({
                    "compliant": False,
                    "violated_constraints": ["No layoffs"],
                    "reason": "Task suggests layoffs",
                })
            )
        )

        critic = PolicyCritic(client=client)
        result = await critic.evaluate(
            _make_subtask("Suggest cost reduction through workforce changes"),
            constraints=["No layoffs"],
        )

        assert result.passed is False
        assert "No layoffs" in result.evidence

    @pytest.mark.asyncio
    async def test_parse_error_returns_fail_safe(self):
        client = AsyncMock()
        client.messages.create = AsyncMock(
            return_value=_mock_claude_response("not json at all!!!")
        )

        critic = PolicyCritic(client=client)
        result = await critic.evaluate(_make_subtask(), constraints=["test"])

        assert result.passed is False
        assert "fail-safe" in result.evidence


# ─── CriticPipeline ───────────────────────────────────────


class TestCriticPipeline:
    """CriticPipeline orchestrates all critics."""

    @pytest.mark.asyncio
    async def test_all_pass(self):
        safety = AsyncMock(spec=SafetyCritic)
        safety.evaluate = AsyncMock(
            return_value=[
                ProofObligation(
                    axiom_id=i, axiom_name=f"A{i}", description="", passed=True, evidence=""
                )
                for i in range(5)
            ]
        )

        feasibility = AsyncMock(spec=FeasibilityCritic)
        feasibility.evaluate = AsyncMock(
            return_value=ProofObligation(
                axiom_id=0, axiom_name="Feasibility", description="", passed=True, evidence="ok"
            )
        )

        policy = AsyncMock(spec=PolicyCritic)
        policy.evaluate = AsyncMock(
            return_value=ProofObligation(
                axiom_id=0, axiom_name="Policy", description="", passed=True, evidence="ok"
            )
        )

        pipeline = CriticPipeline(safety=safety, feasibility=feasibility, policy=policy)
        passed, obligations = await pipeline.evaluate(_make_subtask(), constraints=[])

        assert passed is True
        assert len(obligations) == 7  # 5 safety + 1 feasibility + 1 policy

    @pytest.mark.asyncio
    async def test_safety_fails(self):
        safety = AsyncMock(spec=SafetyCritic)
        safety.evaluate = AsyncMock(
            return_value=[
                ProofObligation(
                    axiom_id=1, axiom_name="Human Agency", description="",
                    passed=False, evidence="violates override",
                )
            ]
        )

        feasibility = AsyncMock(spec=FeasibilityCritic)
        feasibility.evaluate = AsyncMock(
            return_value=ProofObligation(
                axiom_id=0, axiom_name="Feasibility", description="", passed=True, evidence=""
            )
        )

        policy = AsyncMock(spec=PolicyCritic)
        policy.evaluate = AsyncMock(
            return_value=ProofObligation(
                axiom_id=0, axiom_name="Policy", description="", passed=True, evidence=""
            )
        )

        pipeline = CriticPipeline(safety=safety, feasibility=feasibility, policy=policy)
        passed, obligations = await pipeline.evaluate(_make_subtask(), constraints=[])

        assert passed is False

    @pytest.mark.asyncio
    async def test_feasibility_fails(self):
        safety = AsyncMock(spec=SafetyCritic)
        safety.evaluate = AsyncMock(
            return_value=[
                ProofObligation(
                    axiom_id=1, axiom_name="A1", description="", passed=True, evidence=""
                )
            ]
        )

        feasibility = AsyncMock(spec=FeasibilityCritic)
        feasibility.evaluate = AsyncMock(
            return_value=ProofObligation(
                axiom_id=0, axiom_name="Feasibility", description="",
                passed=False, evidence="cannot do",
            )
        )

        policy = AsyncMock(spec=PolicyCritic)
        policy.evaluate = AsyncMock(
            return_value=ProofObligation(
                axiom_id=0, axiom_name="Policy", description="", passed=True, evidence=""
            )
        )

        pipeline = CriticPipeline(safety=safety, feasibility=feasibility, policy=policy)
        passed, _ = await pipeline.evaluate(_make_subtask(), constraints=[])

        assert passed is False

    def test_create_trace_passed(self):
        subtask = _make_subtask("Analyze data")
        obligations = [
            ProofObligation(axiom_id=1, axiom_name="A1", description="", passed=True, evidence="")
        ]
        trace = CriticPipeline.create_trace(subtask, True, obligations, "intent-1")

        assert trace.event_type == "CRITIC_PIPELINE"
        assert "PASSED" in trace.description
        assert trace.l0_passed is True

    def test_create_trace_rejected(self):
        subtask = _make_subtask("Dangerous action")
        obligations = [
            ProofObligation(
                axiom_id=1, axiom_name="Safety", description="", passed=False, evidence="bad"
            )
        ]
        trace = CriticPipeline.create_trace(subtask, False, obligations, "intent-1")

        assert "REJECTED" in trace.description
        assert trace.l0_passed is False
        assert len(trace.details["failed"]) == 1
