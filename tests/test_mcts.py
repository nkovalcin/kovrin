"""Tests for LATTICE MCTS Decomposition Explorer."""

import json
from unittest.mock import AsyncMock, MagicMock

import pytest

from kovrin.core.models import (
    DecompositionCandidate,
    MCTSNode,
    SubTask,
)
from kovrin.engine.mcts import (
    _VARIANT_INSTRUCTIONS,
    PROMPT_VARIANTS,
    CriticBasedScorer,
    MCTSExplorer,
)
from kovrin.intent.schema import IntentV2


def _make_subtasks(n=3, prefix="task"):
    return [SubTask(id=f"{prefix}_{i}", description=f"Task {i}") for i in range(n)]


class TestCriticBasedScorer:
    @pytest.mark.asyncio
    async def test_score_all_pass(self):
        critics = AsyncMock()
        critics.evaluate = AsyncMock(return_value=(True, []))
        scorer = CriticBasedScorer(critics)

        candidate = DecompositionCandidate(subtasks=_make_subtasks(3))
        score = await scorer.score(candidate, [], "test intent", None)

        assert score == pytest.approx(1.0)
        assert candidate.critic_pass_rate == pytest.approx(1.0)

    @pytest.mark.asyncio
    async def test_score_partial_pass(self):
        critics = AsyncMock()
        call_count = 0

        async def alternate_evaluate(**kwargs):
            nonlocal call_count
            call_count += 1
            return (call_count % 2 == 1, [])

        critics.evaluate = alternate_evaluate
        scorer = CriticBasedScorer(critics)

        candidate = DecompositionCandidate(subtasks=_make_subtasks(4))
        score = await scorer.score(candidate, [], "test intent", None)

        # 2 out of 4 pass
        assert candidate.critic_pass_rate == pytest.approx(0.5)

    @pytest.mark.asyncio
    async def test_score_empty_subtasks(self):
        critics = AsyncMock()
        scorer = CriticBasedScorer(critics)

        candidate = DecompositionCandidate(subtasks=[])
        score = await scorer.score(candidate, [], "test intent", None)
        assert score == 0.0

    @pytest.mark.asyncio
    async def test_score_penalty_for_many_tasks(self):
        critics = AsyncMock()
        critics.evaluate = AsyncMock(return_value=(True, []))
        scorer = CriticBasedScorer(critics)

        # 10 tasks — penalty = (10-8) * 0.05 = 0.1
        candidate = DecompositionCandidate(subtasks=_make_subtasks(10))
        score = await scorer.score(candidate, [], "test", None)

        # pass_rate = 1.0, penalty = 0.1, score = 0.9
        assert score == pytest.approx(0.9)

    @pytest.mark.asyncio
    async def test_score_no_penalty_under_threshold(self):
        critics = AsyncMock()
        critics.evaluate = AsyncMock(return_value=(True, []))
        scorer = CriticBasedScorer(critics)

        candidate = DecompositionCandidate(subtasks=_make_subtasks(5))
        score = await scorer.score(candidate, [], "test", None)
        assert score == pytest.approx(1.0)


class TestPromptVariants:
    def test_all_variants_defined(self):
        assert len(PROMPT_VARIANTS) == 5
        for v in PROMPT_VARIANTS:
            assert v in _VARIANT_INSTRUCTIONS

    def test_default_has_empty_instruction(self):
        assert _VARIANT_INSTRUCTIONS["default"] == ""

    def test_other_variants_have_content(self):
        for v in PROMPT_VARIANTS:
            if v != "default":
                assert len(_VARIANT_INSTRUCTIONS[v]) > 0


class TestMCTSExplorer:
    def _make_explorer(self, parser=None, scorer=None, client=None, **kwargs):
        parser = parser or AsyncMock()
        scorer = scorer or AsyncMock()
        client = client or AsyncMock()
        return MCTSExplorer(parser=parser, scorer=scorer, client=client, **kwargs)

    def test_ucb1_selection_prefers_unexplored(self):
        explorer = self._make_explorer()

        root = MCTSNode(id="root", visits=5, total_reward=3.0)
        child1 = MCTSNode(id="c1", visits=3, total_reward=1.5, parent_id="root")
        child2 = MCTSNode(id="c2", visits=0, total_reward=0.0, parent_id="root")
        root.children = ["c1", "c2"]

        explorer._nodes = {"root": root, "c1": child1, "c2": child2}
        selected = explorer._select(root)
        assert selected.id == "c2"  # Unexplored child preferred

    def test_ucb1_selection_with_all_visited(self):
        explorer = self._make_explorer()

        root = MCTSNode(id="root", visits=10, total_reward=5.0)
        child1 = MCTSNode(id="c1", visits=5, total_reward=4.0, parent_id="root")
        child2 = MCTSNode(id="c2", visits=5, total_reward=1.0, parent_id="root")
        root.children = ["c1", "c2"]

        explorer._nodes = {"root": root, "c1": child1, "c2": child2}
        selected = explorer._select(root)
        # child1 has higher exploit (4/5=0.8 vs 1/5=0.2), same explore
        assert selected.id == "c1"

    def test_backpropagation(self):
        explorer = self._make_explorer()

        root = MCTSNode(id="root", visits=1, total_reward=0.5)
        child = MCTSNode(id="c1", visits=1, total_reward=0.8, parent_id="root")

        explorer._nodes = {"root": root, "c1": child}
        explorer._backpropagate(child, 0.9)

        assert child.visits == 2
        assert child.total_reward == pytest.approx(1.7)
        assert root.visits == 2
        assert root.total_reward == pytest.approx(1.4)

    @pytest.mark.asyncio
    async def test_expand_respects_max_children(self):
        explorer = self._make_explorer(max_children=2)
        intent = IntentV2.simple(description="Test")

        parent = MCTSNode(id="root", children=["c1", "c2"])
        explorer._nodes = {"root": parent}

        result = await explorer._expand(parent, intent, [], None, 0)
        assert result is None  # max_children reached

    @pytest.mark.asyncio
    async def test_explore_returns_best_and_all(self):
        parser = AsyncMock()
        parser.parse = AsyncMock(return_value=_make_subtasks(2))
        parser.MODEL = "claude-sonnet-4-6"
        parser._parse_response = MagicMock(return_value=_make_subtasks(2, "variant"))

        scorer = AsyncMock()
        call_count = 0

        async def mock_score(candidate, constraints, intent_context, task_context):
            nonlocal call_count
            call_count += 1
            candidate.score = 0.5 + (call_count * 0.1)
            candidate.critic_pass_rate = candidate.score
            return candidate.score

        scorer.score = mock_score

        client = AsyncMock()
        response = MagicMock()
        response.content = [MagicMock()]
        response.content[0].text = json.dumps(
            [
                {"description": "V task 1", "risk_level": "LOW"},
                {"description": "V task 2", "risk_level": "LOW"},
            ]
        )
        client.messages.create = AsyncMock(return_value=response)

        explorer = MCTSExplorer(
            parser=parser,
            scorer=scorer,
            client=client,
            max_iterations=3,
        )

        intent = IntentV2.simple(description="Test intent")
        best, all_candidates = await explorer.explore(intent, ["constraint1"])

        assert best is not None
        assert len(all_candidates) > 1
        # Best should have highest score
        assert best.score == max(c.score for c in all_candidates)

    @pytest.mark.asyncio
    async def test_explore_with_zero_iterations(self):
        parser = AsyncMock()
        parser.parse = AsyncMock(return_value=_make_subtasks(2))

        scorer = AsyncMock()

        async def mock_score(candidate, constraints, intent_context, task_context):
            candidate.score = 0.8
            candidate.critic_pass_rate = 0.8
            return 0.8

        scorer.score = mock_score

        explorer = MCTSExplorer(
            parser=parser,
            scorer=scorer,
            client=AsyncMock(),
            max_iterations=0,
        )

        intent = IntentV2.simple(description="Test")
        best, all_candidates = await explorer.explore(intent)

        # Only root candidate
        assert len(all_candidates) == 1
        assert best.score == pytest.approx(0.8)

    def test_nodes_property(self):
        explorer = self._make_explorer()
        assert explorer.nodes == {}
        explorer._nodes["test"] = MCTSNode(id="test")
        nodes = explorer.nodes
        assert "test" in nodes
        # Should be a copy
        assert nodes is not explorer._nodes
