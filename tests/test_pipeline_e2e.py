"""End-to-end tests for the Kovrin core pipeline.

Tests the full flow: intent → parse → critics → route → execute → audit trail.
All external dependencies (Claude API) are mocked.
"""

import json
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin import Kovrin
from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import (
    ExecutionResult,
    ProofObligation,
    RiskLevel,
    RoutingAction,
    SpeculationTier,
    SubTask,
    TaskStatus,
)


def _mock_claude_response(text: str) -> MagicMock:
    """Create a mock Anthropic message response."""
    msg = MagicMock()
    content_block = MagicMock()
    content_block.text = text
    msg.content = [content_block]
    return msg


def _make_subtask(
    task_id: str = "t-1",
    desc: str = "Analyze data",
    risk: RiskLevel = RiskLevel.LOW,
    tier: SpeculationTier = SpeculationTier.FREE,
    deps: list[str] | None = None,
) -> SubTask:
    return SubTask(
        id=task_id,
        description=desc,
        risk_level=risk,
        speculation_tier=tier,
        dependencies=deps or [],
    )


# ─── Full Pipeline: Happy Path ───────────────────────────────


class TestFullPipelineHappyPath:
    """Intent → decompose → approve → execute → audit."""

    @pytest.mark.asyncio
    async def test_single_task_pipeline(self):
        """Simplest case: single LOW/FREE task, auto-approved, executed."""
        engine = Kovrin(api_key="test-key")

        subtasks = [_make_subtask("t-1", "Search for AI news")]

        # Mock parser
        engine._parser.parse = AsyncMock(return_value=subtasks)

        # Mock critics — all pass
        engine._critics.evaluate = AsyncMock(
            return_value=(
                True,
                [
                    ProofObligation(
                        axiom_id=i,
                        axiom_name=f"A{i}",
                        description="",
                        passed=True,
                        evidence="ok",
                    )
                    for i in range(5)
                ],
            )
        )

        # Mock graph executor
        engine._graph_executor.execute = AsyncMock(
            return_value={"t-1": "Found 5 articles about AI safety"}
        )

        result = await engine.run(
            intent="Search for recent AI safety news",
            constraints=["Focus on 2026"],
        )

        assert result.success is True
        assert "AI safety" in result.output
        assert result.intent_id is not None
        assert len(result.traces) > 0

        # Verify trace event types present
        event_types = [t.event_type for t in result.traces]
        assert "INTENT_RECEIVED" in event_types
        assert "DECOMPOSITION" in event_types
        assert "CRITIC_PIPELINE" in event_types
        assert "EXECUTION_START" in event_types
        assert "PIPELINE_COMPLETE" in event_types

    @pytest.mark.asyncio
    async def test_multi_task_pipeline(self):
        """Multiple tasks with dependencies, all approved."""
        engine = Kovrin(api_key="test-key")

        subtasks = [
            _make_subtask("t-1", "Gather expense data"),
            _make_subtask("t-2", "Analyze trends", deps=["t-1"]),
            _make_subtask("t-3", "Generate summary", deps=["t-2"]),
        ]

        engine._parser.parse = AsyncMock(return_value=subtasks)
        engine._critics.evaluate = AsyncMock(return_value=(True, []))
        engine._graph_executor.execute = AsyncMock(
            return_value={
                "t-1": "Data gathered",
                "t-2": "Trends analyzed: costs up 15%",
                "t-3": "Summary: operational costs increased",
            }
        )

        result = await engine.run(
            intent="Analyze monthly expenses and suggest savings",
            constraints=["No layoffs"],
        )

        assert result.success is True
        assert len(result.sub_tasks) == 3
        assert "costs" in result.output.lower()

    @pytest.mark.asyncio
    async def test_trace_log_provided_externally(self):
        """Pipeline should use externally provided trace log."""
        engine = Kovrin(api_key="test-key")
        external_log = ImmutableTraceLog()

        subtasks = [_make_subtask("t-1", "Quick task")]
        engine._parser.parse = AsyncMock(return_value=subtasks)
        engine._critics.evaluate = AsyncMock(return_value=(True, []))
        engine._graph_executor.execute = AsyncMock(return_value={"t-1": "Done"})

        result = await engine.run(
            intent="Quick check",
            trace_log=external_log,
        )

        assert result.success is True
        # External trace log should have events
        events = external_log.get_events()
        assert len(events) > 0


# ─── All Tasks Rejected ──────────────────────────────────────


class TestAllTasksRejected:
    """Pipeline aborts when all tasks are rejected by critics."""

    @pytest.mark.asyncio
    async def test_all_rejected_aborts_pipeline(self):
        engine = Kovrin(api_key="test-key")

        subtasks = [
            _make_subtask("t-1", "Dangerous action", RiskLevel.CRITICAL),
        ]

        engine._parser.parse = AsyncMock(return_value=subtasks)
        engine._critics.evaluate = AsyncMock(
            return_value=(
                False,
                [
                    ProofObligation(
                        axiom_id=1,
                        axiom_name="Human Agency",
                        description="Violates human override",
                        passed=False,
                        evidence="Task removes human control",
                    )
                ],
            )
        )

        result = await engine.run(intent="Do something dangerous")

        assert result.success is False
        assert "rejected" in result.output.lower()
        assert len(result.rejected_tasks) == 1
        assert result.rejected_tasks[0].status == TaskStatus.REJECTED_BY_L0

    @pytest.mark.asyncio
    async def test_partial_rejection_continues(self):
        """If some tasks are rejected but others pass, pipeline continues with approved ones."""
        engine = Kovrin(api_key="test-key")

        subtasks = [
            _make_subtask("t-1", "Safe analysis", RiskLevel.LOW),
            _make_subtask("t-2", "Dangerous deletion", RiskLevel.CRITICAL),
        ]

        engine._parser.parse = AsyncMock(return_value=subtasks)

        # First call approves, second rejects
        engine._critics.evaluate = AsyncMock(
            side_effect=[
                (True, []),
                (
                    False,
                    [
                        ProofObligation(
                            axiom_id=1,
                            axiom_name="Harm Floor",
                            description="",
                            passed=False,
                            evidence="Exceeds harm threshold",
                        )
                    ],
                ),
            ]
        )

        engine._graph_executor.execute = AsyncMock(
            return_value={"t-1": "Analysis complete"}
        )

        result = await engine.run(intent="Analyze and then delete old data")

        assert result.success is True
        assert len(result.rejected_tasks) == 1
        assert result.rejected_tasks[0].id == "t-2"


# ─── Merkle Audit Trail Integrity ────────────────────────────


class TestAuditTrailIntegrity:
    """Every pipeline run must produce a verifiable Merkle chain."""

    @pytest.mark.asyncio
    async def test_trace_chain_integrity(self):
        """All trace events form a valid Merkle hash chain."""
        engine = Kovrin(api_key="test-key")
        trace_log = ImmutableTraceLog()

        subtasks = [_make_subtask("t-1", "Do work")]
        engine._parser.parse = AsyncMock(return_value=subtasks)
        engine._critics.evaluate = AsyncMock(return_value=(True, []))
        engine._graph_executor.execute = AsyncMock(return_value={"t-1": "Done"})

        await engine.run(intent="Simple task", trace_log=trace_log)

        # Verify the Merkle chain is intact
        valid, _ = trace_log.verify_integrity()
        assert valid is True

    @pytest.mark.asyncio
    async def test_rejected_pipeline_also_has_integrity(self):
        """Even when all tasks are rejected, the trace chain is valid."""
        engine = Kovrin(api_key="test-key")
        trace_log = ImmutableTraceLog()

        subtasks = [_make_subtask("t-1", "Bad task")]
        engine._parser.parse = AsyncMock(return_value=subtasks)
        engine._critics.evaluate = AsyncMock(return_value=(False, []))

        await engine.run(intent="Bad intent", trace_log=trace_log)

        valid, _ = trace_log.verify_integrity()
        assert valid is True
        events = trace_log.get_events()
        assert len(events) >= 3  # INTENT_RECEIVED, DECOMPOSITION, CRITIC_PIPELINE, PIPELINE_ABORTED

    @pytest.mark.asyncio
    async def test_trace_events_have_correct_intent_id(self):
        """All trace events reference the same intent_id."""
        engine = Kovrin(api_key="test-key")
        trace_log = ImmutableTraceLog()

        subtasks = [_make_subtask("t-1", "Work")]
        engine._parser.parse = AsyncMock(return_value=subtasks)
        engine._critics.evaluate = AsyncMock(return_value=(True, []))
        engine._graph_executor.execute = AsyncMock(return_value={"t-1": "Done"})

        result = await engine.run(intent="Test", trace_log=trace_log)

        for event in trace_log.get_events():
            assert event.trace.intent_id == result.intent_id


# ─── Safety Invariants ───────────────────────────────────────


class TestSafetyInvariantsE2E:
    """Verify the 6 safety invariants hold end-to-end."""

    @pytest.mark.asyncio
    async def test_rejected_task_never_executes(self):
        """Invariant #6: Rejected tasks must NEVER reach the executor."""
        engine = Kovrin(api_key="test-key")

        subtasks = [_make_subtask("t-1", "Rejected task")]
        engine._parser.parse = AsyncMock(return_value=subtasks)
        engine._critics.evaluate = AsyncMock(return_value=(False, []))

        # If executor is called, this will fail
        engine._graph_executor.execute = AsyncMock(
            side_effect=AssertionError("Executor should not be called for rejected tasks")
        )

        result = await engine.run(intent="Bad intent")

        assert result.success is False
        # Executor should NOT have been called
        engine._graph_executor.execute.assert_not_called()

    @pytest.mark.asyncio
    async def test_critical_always_human_approval(self):
        """Invariant #2: CRITICAL risk always routes to HUMAN_APPROVAL."""
        from kovrin.engine.risk_router import RiskRouter

        router = RiskRouter()

        for tier in SpeculationTier:
            task = _make_subtask("t-crit", "Critical task", RiskLevel.CRITICAL, tier)
            decision = router.route(task)
            assert decision.action == RoutingAction.HUMAN_APPROVAL, (
                f"CRITICAL + {tier.value} must be HUMAN_APPROVAL, got {decision.action.value}"
            )

    @pytest.mark.asyncio
    async def test_merkle_chain_append_only(self):
        """Invariant #3: Merkle chain is append-only, never modified."""
        trace_log = ImmutableTraceLog()
        from kovrin.core.models import Trace

        # Add events
        for i in range(5):
            trace_log.append(
                Trace(
                    intent_id="test",
                    event_type=f"EVENT_{i}",
                    description=f"Event {i}",
                )
            )

        # Verify integrity
        valid, _ = trace_log.verify_integrity()
        assert valid is True

        # Add more events
        trace_log.append(
            Trace(intent_id="test", event_type="FINAL", description="Final event")
        )

        # Still valid
        valid, _ = trace_log.verify_integrity()
        assert valid is True
        assert len(trace_log.get_events()) == 6


# ─── Pipeline with Options ───────────────────────────────────


class TestPipelineOptions:
    """Test pipeline with various initialization options."""

    @pytest.mark.asyncio
    async def test_pipeline_with_tools_enabled(self):
        """Pipeline initializes correctly with tools=True."""
        engine = Kovrin(api_key="test-key", tools=True)

        assert engine._tools_enabled is True
        assert engine._tool_registry is not None
        assert engine._tool_router is not None

        # Verify built-in tools are registered
        all_tools = engine._tool_registry.get_all()
        tool_names = [t.name for t in all_tools]
        assert "calculator" in tool_names
        assert "web_search" in tool_names

    @pytest.mark.asyncio
    async def test_pipeline_with_watchdog(self):
        """Pipeline initializes correctly with watchdog=True."""
        engine = Kovrin(api_key="test-key", watchdog=True)
        assert engine._watchdog_enabled is True

    @pytest.mark.asyncio
    async def test_pipeline_with_agents(self):
        """Pipeline initializes correctly with agents=True."""
        engine = Kovrin(api_key="test-key", agents=True)
        assert engine._agents_enabled is True
        assert engine._coordinator is not None
        assert engine._registry is not None

    def test_pipeline_with_custom_model_routing(self):
        """Custom model routing is applied to components."""
        engine = Kovrin(
            api_key="test-key",
            model_routing={
                "intent_parser": "claude-haiku-4-5",
                "task_executor": "claude-opus-4-6",
            },
        )
        assert engine._parser._model == "claude-haiku-4-5"
        assert engine._executor._model == "claude-opus-4-6"


# ─── Graph Construction ──────────────────────────────────────


class TestGraphConstruction:
    """Verify correct ExecutionGraph construction during pipeline."""

    @pytest.mark.asyncio
    async def test_graph_summary_in_result(self):
        """Result includes graph summary with nodes and edges."""
        engine = Kovrin(api_key="test-key")

        subtasks = [
            _make_subtask("t-1", "Step 1"),
            _make_subtask("t-2", "Step 2", deps=["t-1"]),
        ]
        engine._parser.parse = AsyncMock(return_value=subtasks)
        engine._critics.evaluate = AsyncMock(return_value=(True, []))
        engine._graph_executor.execute = AsyncMock(
            return_value={"t-1": "Done", "t-2": "Done"}
        )

        result = await engine.run(intent="Two-step task")

        assert result.graph_summary is not None
        assert "nodes" in result.graph_summary
        assert len(result.graph_summary["nodes"]) == 2

    @pytest.mark.asyncio
    async def test_invalid_dependencies_filtered(self):
        """Dependencies pointing to rejected tasks are filtered out."""
        engine = Kovrin(api_key="test-key")

        subtasks = [
            _make_subtask("t-1", "Good task"),
            _make_subtask("t-2", "Bad task"),
            _make_subtask("t-3", "Depends on bad", deps=["t-2"]),
        ]

        engine._parser.parse = AsyncMock(return_value=subtasks)
        # t-1 passes, t-2 fails, t-3 passes
        engine._critics.evaluate = AsyncMock(
            side_effect=[
                (True, []),
                (False, []),
                (True, []),
            ]
        )
        engine._graph_executor.execute = AsyncMock(
            return_value={"t-1": "Done", "t-3": "Done without dep"}
        )

        result = await engine.run(intent="Mixed task")

        assert result.success is True
        assert len(result.rejected_tasks) == 1
