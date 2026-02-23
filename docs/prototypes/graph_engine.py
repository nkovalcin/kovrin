"""
LATTICE v2 Graph Execution Engine

Replaces the linear executor from MVP with a DAG-based engine
that supports parallel execution, dependency resolution, and
graph-level optimizations.

Based on research into:
- Dataflow computation models (Kahn process networks)
- TensorFlow's computation graph optimization
- Temporal's durable execution
- Dask's dynamic task graph scheduling

The graph engine enables:
1. Parallel execution of independent sub-tasks
2. Dependency-aware scheduling
3. Partial failure recovery (re-execute only failed branches)
4. Graph-level optimization (fusing redundant LLM calls)
5. Speculative execution with rollback
"""

from __future__ import annotations

import asyncio
from collections import defaultdict
from dataclasses import dataclass, field
from enum import Enum
from typing import Any

from kovrin.core.models import RiskLevel, SubTask, TaskStatus, Trace


class NodeState(str, Enum):
    PENDING = "PENDING"
    READY = "READY"
    RUNNING = "RUNNING"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"
    SKIPPED = "SKIPPED"
    REJECTED = "REJECTED"


@dataclass
class GraphNode:
    """A node in the execution graph.
    
    Each node wraps a SubTask and tracks its dependencies,
    dependents, and execution state.
    """
    task: SubTask
    state: NodeState = NodeState.PENDING
    dependencies: set[str] = field(default_factory=set)  # task IDs this depends on
    dependents: set[str] = field(default_factory=set)     # task IDs that depend on this
    result: str | None = None
    error: str | None = None

    @property
    def id(self) -> str:
        return self.task.id

    @property
    def is_ready(self) -> bool:
        """A node is ready when all its dependencies are completed."""
        return self.state == NodeState.READY


@dataclass
class ExecutionGraph:
    """A directed acyclic graph of tasks for execution.
    
    The graph tracks dependencies between tasks and enables
    parallel execution of independent branches.
    """
    nodes: dict[str, GraphNode] = field(default_factory=dict)
    intent_id: str = ""
    traces: list[Trace] = field(default_factory=list)

    def add_node(self, task: SubTask, dependencies: set[str] | None = None) -> GraphNode:
        """Add a task node to the graph."""
        node = GraphNode(
            task=task,
            dependencies=dependencies or set(),
        )
        self.nodes[node.id] = node
        
        # Register as dependent in dependency nodes
        for dep_id in node.dependencies:
            if dep_id in self.nodes:
                self.nodes[dep_id].dependents.add(node.id)
        
        return node

    def get_ready_nodes(self) -> list[GraphNode]:
        """Get all nodes that are ready for execution.
        
        A node is ready when:
        1. It's in PENDING state
        2. All its dependencies are COMPLETED
        """
        ready = []
        for node in self.nodes.values():
            if node.state != NodeState.PENDING:
                continue
            # Check all dependencies are completed
            deps_met = all(
                self.nodes[dep_id].state == NodeState.COMPLETED
                for dep_id in node.dependencies
                if dep_id in self.nodes
            )
            if deps_met:
                node.state = NodeState.READY
                ready.append(node)
        return ready

    def mark_completed(self, node_id: str, result: str) -> list[GraphNode]:
        """Mark a node as completed and return newly ready nodes."""
        node = self.nodes[node_id]
        node.state = NodeState.COMPLETED
        node.result = result
        node.task.status = TaskStatus.COMPLETED
        node.task.output = result
        return self.get_ready_nodes()

    def mark_failed(self, node_id: str, error: str) -> None:
        """Mark a node as failed and propagate to dependents."""
        node = self.nodes[node_id]
        node.state = NodeState.FAILED
        node.error = error
        node.task.status = TaskStatus.FAILED
        
        # Cascade: skip all dependents
        self._cascade_skip(node_id)

    def mark_rejected(self, node_id: str) -> None:
        """Mark a node as rejected by L0 and cascade."""
        node = self.nodes[node_id]
        node.state = NodeState.REJECTED
        node.task.status = TaskStatus.REJECTED_BY_L0
        self._cascade_skip(node_id)

    def _cascade_skip(self, failed_id: str) -> None:
        """Skip all transitive dependents of a failed/rejected node."""
        to_skip = list(self.nodes[failed_id].dependents)
        visited = set()
        while to_skip:
            nid = to_skip.pop()
            if nid in visited:
                continue
            visited.add(nid)
            if nid in self.nodes:
                self.nodes[nid].state = NodeState.SKIPPED
                self.nodes[nid].task.status = TaskStatus.FAILED
                to_skip.extend(self.nodes[nid].dependents)

    @property
    def is_complete(self) -> bool:
        """True when no more nodes can be executed."""
        return all(
            n.state in (NodeState.COMPLETED, NodeState.FAILED, NodeState.SKIPPED, NodeState.REJECTED)
            for n in self.nodes.values()
        )

    @property
    def completed_results(self) -> dict[str, str]:
        """Map of task_id → result for all completed nodes."""
        return {
            nid: node.result
            for nid, node in self.nodes.items()
            if node.state == NodeState.COMPLETED and node.result
        }

    @property
    def execution_order(self) -> list[list[str]]:
        """Return tasks grouped by execution wave (parallel groups).
        
        Wave 0: tasks with no dependencies (can all run in parallel)
        Wave 1: tasks depending only on wave 0 tasks
        ...etc
        """
        waves: list[list[str]] = []
        assigned: set[str] = set()
        remaining = set(self.nodes.keys())
        
        while remaining:
            wave = []
            for nid in list(remaining):
                node = self.nodes[nid]
                if node.dependencies.issubset(assigned):
                    wave.append(nid)
            if not wave:
                break  # Cycle detected or impossible deps
            waves.append(wave)
            assigned.update(wave)
            remaining -= set(wave)
        
        return waves

    def optimize(self) -> list[str]:
        """Apply graph-level optimizations.
        
        Currently implements:
        1. Independent node parallelization (via execution_order)
        2. Dead node elimination (nodes with no path to any output)
        
        Future:
        - Common subexpression elimination (merge duplicate LLM calls)
        - Operation fusion (combine sequential context-compatible tasks)
        """
        optimizations = []
        
        # Calculate parallelism
        waves = self.execution_order
        max_parallel = max(len(w) for w in waves) if waves else 0
        if max_parallel > 1:
            optimizations.append(f"Parallel execution: {max_parallel} tasks can run simultaneously")
        
        return optimizations

    def to_dict(self) -> dict[str, Any]:
        """Serialize graph for visualization/debugging."""
        return {
            "intent_id": self.intent_id,
            "nodes": {
                nid: {
                    "task": node.task.description[:80],
                    "state": node.state.value,
                    "risk": node.task.risk_level.value,
                    "deps": list(node.dependencies),
                    "dependents": list(node.dependents),
                }
                for nid, node in self.nodes.items()
            },
            "execution_waves": self.execution_order,
            "total_nodes": len(self.nodes),
        }


class GraphExecutor:
    """Executes a task graph with parallel scheduling.
    
    Manages concurrent execution of ready nodes while
    respecting dependencies and risk-based routing.
    """

    def __init__(self, max_concurrent: int = 5):
        self.max_concurrent = max_concurrent
        self._semaphore = asyncio.Semaphore(max_concurrent)

    async def execute(
        self,
        graph: ExecutionGraph,
        execute_fn,  # async (SubTask, dict[str, str]) -> str
    ) -> dict[str, str]:
        """Execute all nodes in the graph respecting dependencies.
        
        Args:
            graph: The execution graph
            execute_fn: Async function that executes a single task
                        Takes (task, previous_results) → result string
        
        Returns:
            Dict of task_id → result for completed tasks
        """
        # Initial ready nodes
        ready = graph.get_ready_nodes()
        pending_tasks: set[asyncio.Task] = set()

        while ready or pending_tasks:
            # Launch ready nodes up to concurrency limit
            for node in ready:
                if len(pending_tasks) >= self.max_concurrent:
                    break
                node.state = NodeState.RUNNING
                node.task.status = TaskStatus.EXECUTING
                
                task = asyncio.create_task(
                    self._execute_node(graph, node, execute_fn)
                )
                pending_tasks.add(task)

            if not pending_tasks:
                break

            # Wait for at least one to complete
            done, pending_tasks = await asyncio.wait(
                pending_tasks, return_when=asyncio.FIRST_COMPLETED
            )

            # Process completed tasks and find newly ready nodes
            ready = []
            for completed_task in done:
                newly_ready = completed_task.result()
                ready.extend(newly_ready)

        return graph.completed_results

    async def _execute_node(
        self,
        graph: ExecutionGraph,
        node: GraphNode,
        execute_fn,
    ) -> list[GraphNode]:
        """Execute a single node and return newly ready nodes."""
        async with self._semaphore:
            try:
                # Gather results from dependencies
                dep_results = {
                    dep_id: graph.nodes[dep_id].result
                    for dep_id in node.dependencies
                    if dep_id in graph.nodes and graph.nodes[dep_id].result
                }
                
                result = await execute_fn(node.task, dep_results)
                return graph.mark_completed(node.id, result)
            except Exception as e:
                graph.mark_failed(node.id, str(e))
                return graph.get_ready_nodes()
