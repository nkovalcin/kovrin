"""
Kovrin Beam Search Executor

Maintains top-K execution paths (beams) in parallel.
After each execution wave, the lowest-scoring beams are pruned.

Scoring is based on:
1. Critic validation quality (from decomposition phase)
2. Task execution success rate
"""

import asyncio
from dataclasses import dataclass

from kovrin.core.models import (
    BeamState,
    DecompositionCandidate,
)
from kovrin.engine.graph import ExecutionGraph, GraphNode, NodeState


@dataclass
class Beam:
    """A single execution beam with its own graph and state."""

    id: str
    decomposition: DecompositionCandidate
    graph: ExecutionGraph
    state: BeamState
    score: float = 0.0
    active: bool = True


class BeamSearchExecutor:
    """Executes multiple decomposition candidates as parallel beams.

    Usage:
        executor = BeamSearchExecutor(beam_width=3)
        results, state = await executor.execute(candidates, execute_fn, intent_id)
    """

    def __init__(
        self,
        beam_width: int = 3,
        max_concurrent_per_beam: int = 3,
        prune_after_wave: bool = True,
        min_beams: int = 1,
    ):
        self.beam_width = beam_width
        self._max_concurrent = max_concurrent_per_beam
        self._prune_after_wave = prune_after_wave
        self._min_beams = min_beams
        self._beams_pruned = 0

    async def execute(
        self,
        candidates: list[DecompositionCandidate],
        execute_fn,
        intent_id: str = "",
    ) -> tuple[dict[str, str], BeamState]:
        """Execute top-K candidates as parallel beams.

        Args:
            candidates: Scored decomposition candidates.
            execute_fn: async (SubTask, dict[str, str]) -> str
            intent_id: For graph construction.

        Returns:
            (results_dict, winning_beam_state)
        """
        sorted_candidates = sorted(candidates, key=lambda c: c.score, reverse=True)
        top_k = sorted_candidates[: self.beam_width]

        beams: list[Beam] = []
        for candidate in top_k:
            graph = self._build_graph(candidate, intent_id)
            state = BeamState(
                decomposition_id=candidate.id,
                score=candidate.score,
            )
            beam = Beam(
                id=state.id,
                decomposition=candidate,
                graph=graph,
                state=state,
                score=candidate.score,
            )
            beams.append(beam)

        if not beams:
            return {}, BeamState()

        # Execute wave by wave
        max_waves = max(len(b.graph.execution_order) for b in beams) if beams else 0

        for wave_idx in range(max_waves):
            active_beams = [b for b in beams if b.active]
            if not active_beams:
                break

            # Execute current wave for all active beams in parallel
            await asyncio.gather(
                *[self._execute_wave(beam, wave_idx, execute_fn) for beam in active_beams],
                return_exceptions=True,
            )

            # Prune after each wave
            if self._prune_after_wave and len(active_beams) > self._min_beams:
                self._prune_beams(beams)

        # Select winning beam
        active_beams = [b for b in beams if b.active]
        if not active_beams:
            active_beams = beams

        winner = max(active_beams, key=lambda b: b.score)
        return winner.graph.completed_results, winner.state

    async def _execute_wave(
        self,
        beam: Beam,
        wave_idx: int,
        execute_fn,
    ) -> None:
        """Execute one wave of tasks for a beam."""
        waves = beam.graph.execution_order
        if wave_idx >= len(waves):
            return

        wave_task_ids = waves[wave_idx]
        semaphore = asyncio.Semaphore(self._max_concurrent)

        async def run_node(node: GraphNode):
            async with semaphore:
                try:
                    dep_results = {
                        dep_id: beam.graph.nodes[dep_id].result
                        for dep_id in node.dependencies
                        if dep_id in beam.graph.nodes and beam.graph.nodes[dep_id].result
                    }
                    node.state = NodeState.RUNNING
                    result = await execute_fn(node.task, dep_results)
                    beam.graph.mark_completed(node.id, result)
                    beam.state.completed_tasks[node.id] = result
                except Exception as e:
                    beam.graph.mark_failed(node.id, str(e))

        # Get nodes for this wave that are still pending or newly ready
        ready_nodes = []
        for tid in wave_task_ids:
            if tid in beam.graph.nodes:
                node = beam.graph.nodes[tid]
                if node.state in (NodeState.PENDING, NodeState.READY):
                    node.state = NodeState.READY
                    ready_nodes.append(node)

        await asyncio.gather(
            *[run_node(node) for node in ready_nodes],
            return_exceptions=True,
        )

        beam.state.wave_index = wave_idx + 1
        beam.score = self._score_beam(beam)

    def _score_beam(self, beam: Beam) -> float:
        """Score a beam based on execution progress and quality."""
        total = len(beam.graph.nodes)
        if total == 0:
            return 0.0

        completed = sum(1 for n in beam.graph.nodes.values() if n.state == NodeState.COMPLETED)

        success_rate = completed / total
        base_score = beam.decomposition.critic_pass_rate
        return (base_score * 0.4) + (success_rate * 0.6)

    def _prune_beams(self, beams: list[Beam]) -> None:
        """Prune lowest-scoring beams, keeping at least min_beams active."""
        active = [b for b in beams if b.active]
        if len(active) <= self._min_beams:
            return

        active.sort(key=lambda b: b.score)

        # Prune at most one per wave
        prune_count = min(len(active) - self._min_beams, 1)
        for i in range(prune_count):
            active[i].active = False
            active[i].state.active = False
            self._beams_pruned += 1

    def _build_graph(self, candidate: DecompositionCandidate, intent_id: str) -> ExecutionGraph:
        """Build an ExecutionGraph from a DecompositionCandidate."""
        graph = ExecutionGraph(intent_id=intent_id)
        task_ids = {t.id for t in candidate.subtasks}
        for task in candidate.subtasks:
            valid_deps = {d for d in task.dependencies if d in task_ids}
            graph.add_node(task, valid_deps)
        return graph

    @property
    def beams_pruned(self) -> int:
        return self._beams_pruned
