"""Tests for LATTICE Beam Search Executor."""

import asyncio
from unittest.mock import AsyncMock

import pytest

from kovrin.core.models import (
    BeamState,
    DecompositionCandidate,
    SubTask,
)
from kovrin.engine.beam_search import Beam, BeamSearchExecutor
from kovrin.engine.graph import ExecutionGraph, NodeState


def _make_candidate(n_tasks=2, score=0.8, prefix="t"):
    tasks = [
        SubTask(id=f"{prefix}_{i}", description=f"Task {i}")
        for i in range(n_tasks)
    ]
    return DecompositionCandidate(
        subtasks=tasks,
        score=score,
        critic_pass_rate=score,
    )


class TestBeamSearchExecutor:
    @pytest.mark.asyncio
    async def test_single_beam_execution(self):
        executor = BeamSearchExecutor(beam_width=1)
        candidate = _make_candidate(2, score=0.9)

        async def execute_fn(task, deps):
            return f"Result for {task.id}"

        results, state = await executor.execute([candidate], execute_fn, "i-1")

        assert len(results) == 2
        assert state.decomposition_id == candidate.id

    @pytest.mark.asyncio
    async def test_multi_beam_execution(self):
        executor = BeamSearchExecutor(beam_width=3, min_beams=1)

        c1 = _make_candidate(2, score=0.9, prefix="a")
        c2 = _make_candidate(2, score=0.7, prefix="b")
        c3 = _make_candidate(2, score=0.5, prefix="c")

        async def execute_fn(task, deps):
            return f"Result for {task.id}"

        results, state = await executor.execute([c1, c2, c3], execute_fn, "i-1")

        assert len(results) > 0
        # Winner should have the highest score overall
        assert state is not None

    @pytest.mark.asyncio
    async def test_empty_candidates(self):
        executor = BeamSearchExecutor(beam_width=3)
        results, state = await executor.execute([], AsyncMock(), "i-1")
        assert results == {}

    @pytest.mark.asyncio
    async def test_beam_pruning(self):
        executor = BeamSearchExecutor(beam_width=3, min_beams=1, prune_after_wave=True)

        c1 = _make_candidate(2, score=0.9, prefix="a")
        c2 = _make_candidate(2, score=0.7, prefix="b")
        c3 = _make_candidate(2, score=0.3, prefix="c")

        async def execute_fn(task, deps):
            return f"Result for {task.id}"

        results, state = await executor.execute([c1, c2, c3], execute_fn, "i-1")
        assert executor.beams_pruned > 0

    @pytest.mark.asyncio
    async def test_no_pruning_when_disabled(self):
        executor = BeamSearchExecutor(beam_width=3, prune_after_wave=False)

        c1 = _make_candidate(2, score=0.9, prefix="a")
        c2 = _make_candidate(2, score=0.3, prefix="b")

        async def execute_fn(task, deps):
            return f"Result for {task.id}"

        results, state = await executor.execute([c1, c2], execute_fn, "i-1")
        assert executor.beams_pruned == 0

    @pytest.mark.asyncio
    async def test_handles_execution_errors(self):
        executor = BeamSearchExecutor(beam_width=1)
        candidate = _make_candidate(2, score=0.8)

        call_count = 0

        async def failing_execute_fn(task, deps):
            nonlocal call_count
            call_count += 1
            if call_count == 1:
                raise ValueError("Task failed")
            return "ok"

        results, state = await executor.execute([candidate], failing_execute_fn, "i-1")
        # Some tasks may have failed but execution completes
        assert state is not None

    @pytest.mark.asyncio
    async def test_selects_highest_scoring_winner(self):
        executor = BeamSearchExecutor(beam_width=2, prune_after_wave=False, min_beams=2)

        c1 = _make_candidate(1, score=0.5, prefix="low")
        c2 = _make_candidate(1, score=0.95, prefix="high")

        async def execute_fn(task, deps):
            return "done"

        results, state = await executor.execute([c1, c2], execute_fn, "i-1")
        # The high-scoring candidate should win
        assert state.decomposition_id == c2.id

    @pytest.mark.asyncio
    async def test_tasks_with_dependencies(self):
        """Test beam search handles tasks with inter-dependencies."""
        t1 = SubTask(id="dep_0", description="First task")
        t2 = SubTask(id="dep_1", description="Second task", dependencies=["dep_0"])
        candidate = DecompositionCandidate(
            subtasks=[t1, t2],
            score=0.8,
            critic_pass_rate=0.8,
        )

        executor = BeamSearchExecutor(beam_width=1)

        execution_order = []

        async def ordered_execute_fn(task, deps):
            execution_order.append(task.id)
            return f"Result for {task.id}"

        results, state = await executor.execute([candidate], ordered_execute_fn, "i-1")
        # dep_0 must execute before dep_1
        assert execution_order.index("dep_0") < execution_order.index("dep_1")


class TestBeamScoring:
    def test_score_beam_empty_graph(self):
        executor = BeamSearchExecutor()
        beam = Beam(
            id="b-1",
            decomposition=DecompositionCandidate(critic_pass_rate=0.8),
            graph=ExecutionGraph(),
            state=BeamState(),
        )
        score = executor._score_beam(beam)
        assert score == 0.0

    def test_score_beam_all_completed(self):
        executor = BeamSearchExecutor()
        graph = ExecutionGraph()
        t1 = SubTask(id="t1", description="Task 1")
        node = graph.add_node(t1)
        graph.get_ready_nodes()
        node.state = NodeState.RUNNING
        graph.mark_completed("t1", "done")

        beam = Beam(
            id="b-1",
            decomposition=DecompositionCandidate(critic_pass_rate=0.8),
            graph=graph,
            state=BeamState(),
        )
        score = executor._score_beam(beam)
        # 0.8 * 0.4 + 1.0 * 0.6 = 0.32 + 0.6 = 0.92
        assert score == pytest.approx(0.92)


class TestBeamPruning:
    def test_prune_lowest_beam(self):
        executor = BeamSearchExecutor(min_beams=1)
        beams = [
            Beam(id="b1", decomposition=DecompositionCandidate(), graph=ExecutionGraph(), state=BeamState(), score=0.9, active=True),
            Beam(id="b2", decomposition=DecompositionCandidate(), graph=ExecutionGraph(), state=BeamState(), score=0.3, active=True),
            Beam(id="b3", decomposition=DecompositionCandidate(), graph=ExecutionGraph(), state=BeamState(), score=0.6, active=True),
        ]
        executor._prune_beams(beams)
        # Lowest (0.3) should be pruned
        assert beams[1].active is False
        assert executor.beams_pruned == 1

    def test_prune_respects_min_beams(self):
        executor = BeamSearchExecutor(min_beams=3)
        beams = [
            Beam(id="b1", decomposition=DecompositionCandidate(), graph=ExecutionGraph(), state=BeamState(), score=0.9, active=True),
            Beam(id="b2", decomposition=DecompositionCandidate(), graph=ExecutionGraph(), state=BeamState(), score=0.3, active=True),
            Beam(id="b3", decomposition=DecompositionCandidate(), graph=ExecutionGraph(), state=BeamState(), score=0.6, active=True),
        ]
        executor._prune_beams(beams)
        # All should remain active (min_beams=3)
        assert all(b.active for b in beams)
