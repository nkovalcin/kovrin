"""Tests for LATTICE Graph Execution Engine."""

import asyncio

import pytest

from kovrin.core.models import RiskLevel, SubTask, TaskStatus
from kovrin.engine.graph import ExecutionGraph, GraphExecutor, GraphNode, NodeState


class TestExecutionGraph:
    def test_add_node(self):
        graph = ExecutionGraph()
        task = SubTask(id="t1", description="Task 1")
        node = graph.add_node(task)
        assert node.id == "t1"
        assert "t1" in graph.nodes

    def test_add_node_with_dependencies(self):
        graph = ExecutionGraph()
        t1 = SubTask(id="t1", description="Task 1")
        t2 = SubTask(id="t2", description="Task 2")
        graph.add_node(t1)
        graph.add_node(t2, dependencies={"t1"})
        assert "t1" in graph.nodes["t2"].dependencies
        assert "t2" in graph.nodes["t1"].dependents

    def test_get_ready_nodes_no_deps(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"))
        ready = graph.get_ready_nodes()
        assert len(ready) == 2

    def test_get_ready_nodes_with_deps(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"), dependencies={"t1"})
        ready = graph.get_ready_nodes()
        assert len(ready) == 1
        assert ready[0].id == "t1"

    def test_mark_completed_unlocks_dependents(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"), dependencies={"t1"})

        # Mark t1 ready first
        graph.get_ready_nodes()
        graph.nodes["t1"].state = NodeState.RUNNING

        newly_ready = graph.mark_completed("t1", "Result 1")
        assert len(newly_ready) == 1
        assert newly_ready[0].id == "t2"

    def test_mark_failed_cascades(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"), dependencies={"t1"})
        graph.add_node(SubTask(id="t3", description="Task 3"), dependencies={"t2"})

        graph.mark_failed("t1", "Error")
        assert graph.nodes["t1"].state == NodeState.FAILED
        assert graph.nodes["t2"].state == NodeState.SKIPPED
        assert graph.nodes["t3"].state == NodeState.SKIPPED

    def test_mark_rejected_cascades(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"), dependencies={"t1"})

        graph.mark_rejected("t1")
        assert graph.nodes["t1"].state == NodeState.REJECTED
        assert graph.nodes["t1"].task.status == TaskStatus.REJECTED_BY_L0
        assert graph.nodes["t2"].state == NodeState.SKIPPED

    def test_is_complete(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        assert not graph.is_complete

        graph.nodes["t1"].state = NodeState.COMPLETED
        assert graph.is_complete

    def test_completed_results(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"))

        graph.nodes["t1"].state = NodeState.COMPLETED
        graph.nodes["t1"].result = "Result 1"
        graph.nodes["t2"].state = NodeState.FAILED

        results = graph.completed_results
        assert results == {"t1": "Result 1"}

    def test_execution_order_parallel(self):
        """Two independent tasks should be in the same wave."""
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"))

        waves = graph.execution_order
        assert len(waves) == 1
        assert set(waves[0]) == {"t1", "t2"}

    def test_execution_order_sequential(self):
        """Dependent tasks should be in different waves."""
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"), dependencies={"t1"})
        graph.add_node(SubTask(id="t3", description="Task 3"), dependencies={"t2"})

        waves = graph.execution_order
        assert len(waves) == 3

    def test_execution_order_diamond(self):
        """Diamond dependency: t1 -> t2, t3 -> t4."""
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"), dependencies={"t1"})
        graph.add_node(SubTask(id="t3", description="Task 3"), dependencies={"t1"})
        graph.add_node(SubTask(id="t4", description="Task 4"), dependencies={"t2", "t3"})

        waves = graph.execution_order
        assert len(waves) == 3
        assert waves[0] == ["t1"]
        assert set(waves[1]) == {"t2", "t3"}
        assert waves[2] == ["t4"]

    def test_optimize_detects_parallelism(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"))
        graph.add_node(SubTask(id="t3", description="Task 3"))

        optimizations = graph.optimize()
        assert any("Parallel" in o for o in optimizations)

    def test_to_dict(self):
        graph = ExecutionGraph(intent_id="test-intent")
        graph.add_node(SubTask(id="t1", description="Task 1"))

        data = graph.to_dict()
        assert data["intent_id"] == "test-intent"
        assert data["total_nodes"] == 1
        assert "t1" in data["nodes"]


class TestGraphExecutor:
    @pytest.mark.asyncio
    async def test_execute_single_task(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))

        async def mock_execute(task, deps):
            return f"Result for {task.id}"

        executor = GraphExecutor()
        results = await executor.execute(graph, mock_execute)
        assert results == {"t1": "Result for t1"}

    @pytest.mark.asyncio
    async def test_execute_parallel_tasks(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"))

        execution_order = []

        async def mock_execute(task, deps):
            execution_order.append(task.id)
            return f"Result for {task.id}"

        executor = GraphExecutor(max_concurrent=5)
        results = await executor.execute(graph, mock_execute)
        assert len(results) == 2

    @pytest.mark.asyncio
    async def test_execute_with_dependencies(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"), dependencies={"t1"})

        async def mock_execute(task, deps):
            if task.id == "t2":
                assert "t1" in deps
            return f"Result for {task.id}"

        executor = GraphExecutor()
        results = await executor.execute(graph, mock_execute)
        assert len(results) == 2

    @pytest.mark.asyncio
    async def test_execute_handles_failure(self):
        graph = ExecutionGraph()
        graph.add_node(SubTask(id="t1", description="Task 1"))
        graph.add_node(SubTask(id="t2", description="Task 2"), dependencies={"t1"})

        async def mock_execute(task, deps):
            if task.id == "t1":
                raise RuntimeError("Task failed")
            return "Should not reach here"

        executor = GraphExecutor()
        results = await executor.execute(graph, mock_execute)
        assert len(results) == 0
        assert graph.nodes["t1"].state == NodeState.FAILED
        assert graph.nodes["t2"].state == NodeState.SKIPPED
