"""
Kovrin Automatic Topology Selection

Pure heuristic analysis of execution graphs to recommend the
optimal coordination topology. No Claude API calls — purely
structural analysis for speed.

Topology types:
- SEQUENTIAL: Linear chain (A→B→C)
- PARALLEL: Independent tasks with no edges
- PIPELINE: Multi-stage pipeline with clear waves
- MAP_REDUCE: Fan-out → fan-in pattern (1→N→1)
- HIERARCHICAL: Tree-shaped branching
"""

from kovrin.core.models import TopologyRecommendation, TopologyType, Trace
from kovrin.engine.graph import ExecutionGraph


class TopologyAnalyzer:
    """Analyzes graph structure to recommend execution topology."""

    def analyze(self, graph: ExecutionGraph) -> TopologyRecommendation:
        """Analyze a graph and return a topology recommendation.

        Uses structural heuristics (degree distribution, depth, width)
        to classify the graph into one of the five topology types.
        """
        if not graph.nodes:
            return TopologyRecommendation(
                topology=TopologyType.SEQUENTIAL,
                confidence=0.3,
                reasoning="Empty graph — defaulting to SEQUENTIAL",
            )

        metrics = self._compute_metrics(graph)

        # Decision rules (in priority order)
        topology, confidence, reasoning = self._classify(metrics)

        return TopologyRecommendation(
            topology=topology,
            confidence=confidence,
            reasoning=reasoning,
            graph_metrics=metrics,
        )

    def _compute_metrics(self, graph: ExecutionGraph) -> dict:
        """Compute structural metrics for topology classification."""
        n = len(graph.nodes)

        # Degree distributions
        in_degree: dict[str, int] = {nid: 0 for nid in graph.nodes}
        out_degree: dict[str, int] = {nid: 0 for nid in graph.nodes}

        total_edges = 0
        for nid, node in graph.nodes.items():
            out_degree[nid] = len(node.dependents)
            in_degree[nid] = len(node.dependencies)
            total_edges += len(node.dependents)

        # Roots (no incoming) and leaves (no outgoing)
        roots = [nid for nid, d in in_degree.items() if d == 0]
        leaves = [nid for nid, d in out_degree.items() if d == 0]

        # Execution waves (depth)
        waves = graph.execution_order
        depth = len(waves)
        max_width = max(len(w) for w in waves) if waves else 0

        # Fan-out/fan-in ratios
        max_out = max(out_degree.values()) if out_degree else 0
        max_in = max(in_degree.values()) if in_degree else 0

        return {
            "num_nodes": n,
            "num_edges": total_edges,
            "num_roots": len(roots),
            "num_leaves": len(leaves),
            "depth": depth,
            "max_width": max_width,
            "max_out_degree": max_out,
            "max_in_degree": max_in,
            "roots": roots,
            "leaves": leaves,
        }

    @staticmethod
    def _classify(metrics: dict) -> tuple[TopologyType, float, str]:
        """Classify topology from metrics."""
        n = metrics["num_nodes"]
        edges = metrics["num_edges"]
        depth = metrics["depth"]
        max_width = metrics["max_width"]
        num_roots = metrics["num_roots"]
        num_leaves = metrics["num_leaves"]
        max_out = metrics["max_out_degree"]
        max_in = metrics["max_in_degree"]

        # 1. No edges → PARALLEL
        if edges == 0:
            return (
                TopologyType.PARALLEL,
                0.95,
                f"All {n} tasks are independent (no edges)",
            )

        # 2. Linear chain: each node has at most 1 in and 1 out
        if max_out <= 1 and max_in <= 1 and depth == n:
            return (
                TopologyType.SEQUENTIAL,
                0.95,
                f"Linear chain of {n} tasks",
            )

        # 3. Fan-out→fan-in: 1 root → N intermediates → 1 leaf
        if num_roots == 1 and num_leaves == 1 and max_out >= 2 and max_in >= 2:
            return (
                TopologyType.MAP_REDUCE,
                0.85,
                f"Fan-out({max_out})→fan-in({max_in}) pattern detected",
            )

        # 4. Pipeline: multiple clear waves with max_width > 1
        if depth >= 3 and max_width >= 2 and max_out <= 2 and max_in <= 2:
            return (
                TopologyType.PIPELINE,
                0.75,
                f"Multi-stage pipeline: {depth} stages, max width {max_width}",
            )

        # 5. Tree branching: root fans out, no significant fan-in
        if num_roots <= 2 and max_out >= 2 and max_in <= 1:
            return (
                TopologyType.HIERARCHICAL,
                0.70,
                f"Tree structure: fan-out={max_out}, {num_leaves} leaves",
            )

        # 6. Default fallback
        return (
            TopologyType.SEQUENTIAL,
            0.3,
            f"No clear pattern (nodes={n}, edges={edges}, depth={depth}) — defaulting to SEQUENTIAL",
        )

    @staticmethod
    def create_trace(recommendation: TopologyRecommendation, intent_id: str) -> Trace:
        """Create a TOPOLOGY_SELECTED trace event."""
        return Trace(
            intent_id=intent_id,
            event_type="TOPOLOGY_SELECTED",
            description=f"Topology: {recommendation.topology.value} (confidence={recommendation.confidence:.2f})",
            details={
                "topology": recommendation.topology.value,
                "confidence": recommendation.confidence,
                "reasoning": recommendation.reasoning,
                "metrics": recommendation.graph_metrics,
            },
        )
