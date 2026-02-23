"""Tests for LATTICE Phase 6 — Automatic Topology Selection."""

import pytest

from kovrin.core.models import RiskLevel, SubTask, TopologyRecommendation, TopologyType
from kovrin.engine.graph import ExecutionGraph
from kovrin.engine.topology import TopologyAnalyzer


class TestTopologyModels:
    def test_topology_type_values(self):
        assert TopologyType.SEQUENTIAL == "SEQUENTIAL"
        assert TopologyType.PARALLEL == "PARALLEL"
        assert TopologyType.PIPELINE == "PIPELINE"
        assert TopologyType.MAP_REDUCE == "MAP_REDUCE"
        assert TopologyType.HIERARCHICAL == "HIERARCHICAL"

    def test_recommendation_defaults(self):
        rec = TopologyRecommendation()
        assert rec.topology == TopologyType.SEQUENTIAL
        assert rec.confidence == 0.5
        assert rec.graph_metrics == {}


class TestTopologyAnalyzer:
    def _make_task(self, task_id: str, deps: list[str] | None = None) -> SubTask:
        t = SubTask(description=f"Task {task_id}")
        t.id = task_id
        t.dependencies = deps or []
        return t

    def test_empty_graph(self):
        analyzer = TopologyAnalyzer()
        graph = ExecutionGraph()
        result = analyzer.analyze(graph)
        assert result.topology == TopologyType.SEQUENTIAL
        assert result.confidence <= 0.5

    def test_parallel_no_edges(self):
        """All tasks independent → PARALLEL."""
        analyzer = TopologyAnalyzer()
        graph = ExecutionGraph()
        for i in range(4):
            graph.add_node(self._make_task(f"t{i}"))
        result = analyzer.analyze(graph)
        assert result.topology == TopologyType.PARALLEL
        assert result.confidence >= 0.9

    def test_sequential_chain(self):
        """A→B→C → SEQUENTIAL."""
        analyzer = TopologyAnalyzer()
        graph = ExecutionGraph()
        graph.add_node(self._make_task("a"))
        graph.add_node(self._make_task("b"), {"a"})
        graph.add_node(self._make_task("c"), {"b"})
        result = analyzer.analyze(graph)
        assert result.topology == TopologyType.SEQUENTIAL
        assert result.confidence >= 0.9

    def test_map_reduce_fan_out_fan_in(self):
        """Root→(A,B,C)→Leaf → MAP_REDUCE."""
        analyzer = TopologyAnalyzer()
        graph = ExecutionGraph()
        graph.add_node(self._make_task("root"))
        graph.add_node(self._make_task("a"), {"root"})
        graph.add_node(self._make_task("b"), {"root"})
        graph.add_node(self._make_task("c"), {"root"})
        graph.add_node(self._make_task("leaf"), {"a", "b", "c"})
        result = analyzer.analyze(graph)
        assert result.topology == TopologyType.MAP_REDUCE
        assert result.confidence >= 0.8

    def test_hierarchical_tree(self):
        """Root fans out with no fan-in → HIERARCHICAL."""
        analyzer = TopologyAnalyzer()
        graph = ExecutionGraph()
        graph.add_node(self._make_task("root"))
        graph.add_node(self._make_task("a"), {"root"})
        graph.add_node(self._make_task("b"), {"root"})
        graph.add_node(self._make_task("c"), {"root"})
        # No fan-in — 3 independent leaves
        result = analyzer.analyze(graph)
        assert result.topology == TopologyType.HIERARCHICAL
        assert result.confidence >= 0.6

    def test_single_node(self):
        analyzer = TopologyAnalyzer()
        graph = ExecutionGraph()
        graph.add_node(self._make_task("only"))
        result = analyzer.analyze(graph)
        # Single node with no edges → PARALLEL
        assert result.topology == TopologyType.PARALLEL

    def test_two_node_chain(self):
        analyzer = TopologyAnalyzer()
        graph = ExecutionGraph()
        graph.add_node(self._make_task("a"))
        graph.add_node(self._make_task("b"), {"a"})
        result = analyzer.analyze(graph)
        assert result.topology == TopologyType.SEQUENTIAL

    def test_metrics_populated(self):
        analyzer = TopologyAnalyzer()
        graph = ExecutionGraph()
        graph.add_node(self._make_task("a"))
        graph.add_node(self._make_task("b"), {"a"})
        result = analyzer.analyze(graph)
        assert "num_nodes" in result.graph_metrics
        assert result.graph_metrics["num_nodes"] == 2
        assert "depth" in result.graph_metrics

    def test_confidence_range(self):
        analyzer = TopologyAnalyzer()
        graph = ExecutionGraph()
        for i in range(3):
            graph.add_node(self._make_task(f"t{i}"))
        result = analyzer.analyze(graph)
        assert 0.0 <= result.confidence <= 1.0


class TestTopologyTrace:
    def test_create_trace(self):
        rec = TopologyRecommendation(
            topology=TopologyType.PARALLEL,
            confidence=0.95,
            reasoning="All independent",
        )
        trace = TopologyAnalyzer.create_trace(rec, "intent-1")
        assert trace.event_type == "TOPOLOGY_SELECTED"
        assert "PARALLEL" in trace.description
        assert trace.details["confidence"] == 0.95
        assert trace.intent_id == "intent-1"
