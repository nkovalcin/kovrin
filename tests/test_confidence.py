"""Tests for LATTICE Confidence Estimation."""

import json
from unittest.mock import AsyncMock, MagicMock

import pytest

from kovrin.core.models import ConfidenceEstimate, SubTask
from kovrin.engine.confidence import ConfidenceEstimator


def _mock_client(confidence=0.85, reasoning="Looks good"):
    """Create a mock Anthropic client that returns a confidence response."""
    client = AsyncMock()
    response = MagicMock()
    response.content = [MagicMock()]
    response.content[0].text = json.dumps(
        {
            "confidence": confidence,
            "reasoning": reasoning,
        }
    )
    client.messages.create = AsyncMock(return_value=response)
    return client


class TestConfidenceEstimator:
    @pytest.mark.asyncio
    async def test_estimate_basic(self):
        client = _mock_client(0.9, "High quality output")
        estimator = ConfidenceEstimator(client)
        task = SubTask(id="t-1", description="Analyze data")

        result = await estimator.estimate(task, "Some analysis output", "Analyze sales")
        assert isinstance(result, ConfidenceEstimate)
        assert result.task_id == "t-1"
        assert result.confidence == 0.9
        assert result.reasoning == "High quality output"
        assert result.calibrated is False

    @pytest.mark.asyncio
    async def test_estimate_clamps_to_range(self):
        client = _mock_client(1.5, "Over confident")
        estimator = ConfidenceEstimator(client)
        task = SubTask(id="t-1", description="Test")

        result = await estimator.estimate(task, "output")
        assert result.confidence <= 1.0

    @pytest.mark.asyncio
    async def test_estimate_handles_api_error(self):
        client = AsyncMock()
        client.messages.create = AsyncMock(side_effect=Exception("API down"))
        estimator = ConfidenceEstimator(client)
        task = SubTask(id="t-1", description="Test")

        result = await estimator.estimate(task, "output")
        assert result.confidence == 0.5
        assert "failed" in result.reasoning.lower()
        assert result.calibrated is False

    @pytest.mark.asyncio
    async def test_estimate_handles_malformed_json(self):
        client = AsyncMock()
        response = MagicMock()
        response.content = [MagicMock()]
        response.content[0].text = "This is not JSON at all"
        client.messages.create = AsyncMock(return_value=response)
        estimator = ConfidenceEstimator(client)
        task = SubTask(id="t-1", description="Test")

        result = await estimator.estimate(task, "output")
        assert result.confidence == 0.5

    def test_record_outcome(self):
        client = AsyncMock()
        estimator = ConfidenceEstimator(client, calibration_window=50)
        estimator.record_outcome(0.8, True)
        estimator.record_outcome(0.9, False)
        assert len(estimator._history) == 2

    def test_calibration_not_active_under_threshold(self):
        client = AsyncMock()
        estimator = ConfidenceEstimator(client)
        # Less than 10 samples — raw value returned
        for _ in range(5):
            estimator.record_outcome(0.8, True)
        assert estimator._calibrate(0.8) == 0.8

    def test_calibration_active_over_threshold(self):
        client = AsyncMock()
        estimator = ConfidenceEstimator(client)
        # Add 15 samples near 0.8, all accurate
        for _ in range(15):
            estimator.record_outcome(0.8, True)

        calibrated = estimator._calibrate(0.8)
        # With all True outcomes near 0.8:
        # observed = 1.0, blend = 0.7 * 1.0 + 0.3 * 0.8 = 0.94
        assert calibrated == pytest.approx(0.94, abs=0.01)

    def test_calibration_with_mixed_outcomes(self):
        client = AsyncMock()
        estimator = ConfidenceEstimator(client)
        # 10 accurate, 5 inaccurate near 0.7
        for _ in range(10):
            estimator.record_outcome(0.7, True)
        for _ in range(5):
            estimator.record_outcome(0.7, False)

        calibrated = estimator._calibrate(0.7)
        # observed = 10/15 ≈ 0.667, blend = 0.7 * 0.667 + 0.3 * 0.7 ≈ 0.677
        assert 0.6 < calibrated < 0.75

    def test_calibration_window_limit(self):
        client = AsyncMock()
        estimator = ConfidenceEstimator(client, calibration_window=10)
        for i in range(20):
            estimator.record_outcome(0.5, True)
        assert len(estimator._history) == 10
