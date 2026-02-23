"""Integration tests for LATTICE Phase 4 — Exploration features.

Verifies that:
1. Default mode (explore=False) works identically to Phase 3
2. Exploration features are opt-in and don't affect default behavior
3. New parameters integrate correctly with the Kovrin orchestrator
"""

import json
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin import Kovrin
from kovrin.core.models import (
    DecompositionCandidate,
    ExplorationResult,
    SubTask,
)


def _mock_claude_response(content_text):
    response = MagicMock()
    response.content = [MagicMock()]
    response.content[0].text = content_text
    return response


class TestDefaultBehaviorUnchanged:
    """Ensure explore=False (default) doesn't change existing behavior."""

    def test_default_init_no_exploration(self):
        engine = Kovrin(api_key="test-key")
        assert engine._explore is False
        assert engine._mcts is None
        assert engine._beam_executor is None
        assert engine._confidence is None

    def test_default_beam_width_is_one(self):
        engine = Kovrin(api_key="test-key")
        assert engine._beam_width == 1

    def test_default_confidence_disabled(self):
        engine = Kovrin(api_key="test-key")
        assert engine._enable_confidence is False


class TestExploreInit:
    """Test that explore=True properly initializes MCTS."""

    def test_explore_creates_mcts(self):
        engine = Kovrin(api_key="test-key", explore=True)
        assert engine._explore is True
        assert engine._mcts is not None

    def test_beam_width_creates_executor(self):
        engine = Kovrin(api_key="test-key", beam_width=3)
        assert engine._beam_executor is not None

    def test_confidence_creates_estimator(self):
        engine = Kovrin(api_key="test-key", enable_confidence=True)
        assert engine._confidence is not None

    def test_all_features_combined(self):
        engine = Kovrin(
            api_key="test-key",
            explore=True,
            mcts_iterations=3,
            beam_width=2,
            enable_confidence=True,
        )
        assert engine._mcts is not None
        assert engine._beam_executor is not None
        assert engine._confidence is not None


class TestExplorationPipeline:
    """Test the exploration branch of the pipeline."""

    @pytest.mark.asyncio
    async def test_explore_pipeline_uses_mcts(self):
        """When explore=True, the pipeline should use MCTSExplorer."""
        engine = Kovrin(api_key="test-key", explore=True, mcts_iterations=1)

        subtasks = [
            SubTask(id="t-1", description="Analyze data"),
            SubTask(id="t-2", description="Summarize findings"),
        ]

        best_candidate = DecompositionCandidate(
            subtasks=subtasks,
            score=0.9,
            critic_pass_rate=0.9,
        )

        # Mock MCTS explorer
        engine._mcts.explore = AsyncMock(
            return_value=(best_candidate, [best_candidate])
        )

        # Mock critics to approve all
        engine._critics.evaluate = AsyncMock(return_value=(True, []))

        # Mock executor
        engine._executor.execute_for_graph = AsyncMock(return_value="Task result")

        # Mock graph executor
        engine._graph_executor.execute = AsyncMock(
            return_value={"t-1": "Result 1", "t-2": "Result 2"}
        )

        result = await engine.run(
            intent="Analyze and summarize data",
            constraints=["Be concise"],
        )

        assert result.success is True
        assert result.exploration is not None
        assert result.exploration.candidates_explored == 1
        engine._mcts.explore.assert_called_once()

    @pytest.mark.asyncio
    async def test_non_explore_pipeline_uses_parser(self):
        """When explore=False (default), the pipeline uses IntentParser."""
        engine = Kovrin(api_key="test-key")

        subtasks = [
            SubTask(id="t-1", description="Do work"),
        ]

        # Mock parser
        engine._parser.parse = AsyncMock(return_value=subtasks)

        # Mock critics
        engine._critics.evaluate = AsyncMock(return_value=(True, []))

        # Mock executor
        engine._graph_executor.execute = AsyncMock(
            return_value={"t-1": "Done"}
        )

        result = await engine.run(intent="Do some work")

        assert result.success is True
        assert result.exploration is None
        engine._parser.parse.assert_called_once()


class TestExplorationResult:
    def test_exploration_result_in_execution_result(self):
        from kovrin.core.models import ExecutionResult

        er = ExplorationResult(
            candidates_explored=5,
            best_decomposition_id="dec-abc",
            mcts_iterations=3,
            beam_width=2,
        )
        result = ExecutionResult(intent_id="i-1", exploration=er)
        assert result.exploration.candidates_explored == 5
        assert result.exploration.beam_width == 2

    def test_execution_result_without_exploration(self):
        from kovrin.core.models import ExecutionResult

        result = ExecutionResult(intent_id="i-1")
        assert result.exploration is None
