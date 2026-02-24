"""Tests for LATTICE Phase 6 — Process Reward Model."""

import json
from unittest.mock import AsyncMock, MagicMock

import pytest

from kovrin.core.models import PrmScore, PrmStepScore, RiskLevel, SubTask
from kovrin.engine.prm import ProcessRewardModel

# ─── Model Tests ──────────────────────────────────────────


class TestPrmModels:
    def test_prm_step_score_defaults(self):
        step = PrmStepScore(step_index=0)
        assert step.score == 0.5
        assert step.description == ""
        assert step.reasoning == ""

    def test_prm_step_score_clamped(self):
        step = PrmStepScore(step_index=0, score=0.95)
        assert step.score == 0.95

    def test_prm_score_defaults(self):
        score = PrmScore(task_id="t1")
        assert score.aggregate_score == 0.5
        assert score.step_scores == []
        assert score.timestamp is not None

    def test_prm_score_with_steps(self):
        steps = [
            PrmStepScore(step_index=0, score=0.8),
            PrmStepScore(step_index=1, score=0.6),
        ]
        score = PrmScore(task_id="t1", step_scores=steps, aggregate_score=0.7)
        assert len(score.step_scores) == 2
        assert score.aggregate_score == 0.7


# ─── Weighted Aggregate Tests ─────────────────────────────


class TestWeightedAggregate:
    def test_empty_steps(self):
        assert ProcessRewardModel._weighted_aggregate([]) == 0.5

    def test_single_step(self):
        steps = [PrmStepScore(step_index=0, score=0.8)]
        result = ProcessRewardModel._weighted_aggregate(steps)
        assert 0.79 <= result <= 0.81

    def test_later_steps_weighted_higher(self):
        steps = [
            PrmStepScore(step_index=0, score=0.2),
            PrmStepScore(step_index=1, score=0.8),
        ]
        result = ProcessRewardModel._weighted_aggregate(steps)
        # Later step has higher weight, so aggregate > simple mean 0.5
        assert result > 0.5

    def test_uniform_scores(self):
        steps = [PrmStepScore(step_index=i, score=0.7) for i in range(5)]
        result = ProcessRewardModel._weighted_aggregate(steps)
        assert abs(result - 0.7) < 0.01

    def test_all_zero(self):
        steps = [PrmStepScore(step_index=i, score=0.0) for i in range(3)]
        result = ProcessRewardModel._weighted_aggregate(steps)
        assert result == 0.0

    def test_all_one(self):
        steps = [PrmStepScore(step_index=i, score=1.0) for i in range(3)]
        result = ProcessRewardModel._weighted_aggregate(steps)
        assert result == 1.0


# ─── Threshold Tests ──────────────────────────────────────


class TestThreshold:
    def test_below_threshold(self):
        prm = ProcessRewardModel(AsyncMock(), threshold=0.6)
        score = PrmScore(task_id="t1", aggregate_score=0.4)
        assert prm.is_below_threshold(score) is True

    def test_above_threshold(self):
        prm = ProcessRewardModel(AsyncMock(), threshold=0.6)
        score = PrmScore(task_id="t1", aggregate_score=0.8)
        assert prm.is_below_threshold(score) is False

    def test_at_threshold(self):
        prm = ProcessRewardModel(AsyncMock(), threshold=0.6)
        score = PrmScore(task_id="t1", aggregate_score=0.6)
        assert prm.is_below_threshold(score) is False

    def test_custom_threshold(self):
        prm = ProcessRewardModel(AsyncMock(), threshold=0.8)
        assert prm.threshold == 0.8
        score = PrmScore(task_id="t1", aggregate_score=0.75)
        assert prm.is_below_threshold(score) is True


# ─── Parse Response Tests ─────────────────────────────────


class TestParseResponse:
    def test_valid_json(self):
        prm = ProcessRewardModel(AsyncMock())
        raw = json.dumps(
            {
                "steps": [
                    {"step_index": 0, "description": "Step A", "score": 0.9, "reasoning": "Good"},
                    {"step_index": 1, "description": "Step B", "score": 0.5, "reasoning": "OK"},
                ],
                "overall_reasoning": "Mixed quality",
            }
        )
        result = prm._parse_response(raw, "t1")
        assert len(result.step_scores) == 2
        assert result.step_scores[0].score == 0.9
        assert result.step_scores[1].score == 0.5
        assert result.reasoning == "Mixed quality"
        assert result.task_id == "t1"

    def test_invalid_json(self):
        prm = ProcessRewardModel(AsyncMock())
        result = prm._parse_response("not json", "t1")
        assert result.aggregate_score == 0.5
        assert "Failed to parse" in result.reasoning

    def test_score_clamped_to_range(self):
        prm = ProcessRewardModel(AsyncMock())
        raw = json.dumps(
            {
                "steps": [
                    {"step_index": 0, "score": 1.5},
                    {"step_index": 1, "score": -0.5},
                ],
            }
        )
        result = prm._parse_response(raw, "t1")
        assert result.step_scores[0].score == 1.0
        assert result.step_scores[1].score == 0.0

    def test_empty_steps(self):
        prm = ProcessRewardModel(AsyncMock())
        raw = json.dumps({"steps": []})
        result = prm._parse_response(raw, "t1")
        assert result.aggregate_score == 0.5


# ─── Trace Creation Tests ─────────────────────────────────


class TestPrmTrace:
    def test_create_trace(self):
        task = SubTask(description="Test task", risk_level=RiskLevel.MEDIUM)
        score = PrmScore(
            task_id=task.id,
            aggregate_score=0.75,
            step_scores=[PrmStepScore(step_index=0, score=0.8)],
            reasoning="Good quality",
        )
        trace = ProcessRewardModel.create_trace(task, score, "intent-1")
        assert trace.event_type == "PRM_EVALUATION"
        assert "0.75" in trace.description
        assert trace.details["aggregate_score"] == 0.75
        assert trace.details["step_count"] == 1
        assert trace.risk_level == RiskLevel.MEDIUM


# ─── Evaluate Integration Tests ───────────────────────────


class TestPrmEvaluate:
    @pytest.mark.asyncio
    async def test_evaluate_success(self):
        mock_client = AsyncMock()
        mock_response = MagicMock()
        mock_response.content = [
            MagicMock(
                text=json.dumps(
                    {
                        "steps": [
                            {
                                "step_index": 0,
                                "description": "Analysis",
                                "score": 0.85,
                                "reasoning": "Thorough",
                            },
                        ],
                        "overall_reasoning": "High quality",
                    }
                )
            )
        ]
        mock_client.messages.create = AsyncMock(return_value=mock_response)

        prm = ProcessRewardModel(mock_client)
        task = SubTask(description="Analyze data")
        score = await prm.evaluate(task, "Data analysis result", "Analyze data intent")

        assert score.task_id == task.id
        assert len(score.step_scores) == 1
        assert score.step_scores[0].score == 0.85

    @pytest.mark.asyncio
    async def test_evaluate_api_failure(self):
        mock_client = AsyncMock()
        mock_client.messages.create = AsyncMock(side_effect=Exception("API error"))

        prm = ProcessRewardModel(mock_client)
        task = SubTask(description="Test")
        score = await prm.evaluate(task, "output")

        assert score.aggregate_score == 0.5
        assert "failed" in score.reasoning.lower()
