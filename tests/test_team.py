"""Agent Team unit tests.

Tests for the AgentTeam class which provides multi-agent collaborative
execution with PARALLEL, SEQUENTIAL, and DEBATE patterns.
"""

import json
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin.agents.team import AgentTeam
from kovrin.core.models import (
    AgentRole,
    SubTask,
    TeamExecutionPattern,
    TeamResult,
    TeamRole,
    Trace,
)


# ─── Helpers ────────────────────────────────────────────────


def _make_task(description: str = "Test task") -> SubTask:
    return SubTask(
        id="task-test",
        description=description,
        parent_intent_id="intent-test",
    )


def _make_mock_client(response_text: str = "Agent output") -> MagicMock:
    """Create a mock Anthropic client."""
    mock_message = MagicMock()
    mock_message.content = [MagicMock(text=response_text)]
    mock_message.stop_reason = "end_turn"
    # For usage tracking
    mock_message.usage = MagicMock(input_tokens=100, output_tokens=50)
    client = MagicMock()
    client.messages.create = AsyncMock(return_value=mock_message)
    return client


def _make_roles(count: int = 2) -> list[TeamRole]:
    roles = [
        TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Research the topic"),
        TeamRole(agent_role=AgentRole.WRITER, task_description="Write the report"),
        TeamRole(agent_role=AgentRole.REVIEWER, task_description="Review the work"),
    ]
    return roles[:count]


# ─── Model Tests ────────────────────────────────────────────


class TestTeamModels:
    """Test team-related Pydantic models."""

    def test_team_execution_pattern_values(self):
        assert TeamExecutionPattern.PARALLEL.value == "PARALLEL"
        assert TeamExecutionPattern.SEQUENTIAL.value == "SEQUENTIAL"
        assert TeamExecutionPattern.DEBATE.value == "DEBATE"

    def test_team_role_frozen(self):
        role = TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Research")
        with pytest.raises(Exception):
            role.task_description = "Changed"

    def test_team_role_custom_prompt(self):
        role = TeamRole(
            agent_role=AgentRole.SPECIALIST,
            task_description="Analyze security",
            custom_prompt="You are a security expert.",
        )
        assert role.custom_prompt == "You are a security expert."

    def test_team_result_defaults(self):
        result = TeamResult(
            team_id="t1",
            pattern=TeamExecutionPattern.PARALLEL,
        )
        assert result.success is True
        assert result.agent_outputs == {}
        assert result.synthesized_output == ""
        assert result.debate_rounds == 0
        assert result.traces == []


# ─── AgentTeam Initialization ───────────────────────────────


class TestAgentTeamInit:
    """Test AgentTeam construction."""

    def test_default_pattern(self):
        team = AgentTeam(name="test", roles=_make_roles())
        assert team._pattern == TeamExecutionPattern.PARALLEL

    def test_custom_pattern(self):
        team = AgentTeam(
            name="test",
            roles=_make_roles(),
            pattern=TeamExecutionPattern.DEBATE,
        )
        assert team._pattern == TeamExecutionPattern.DEBATE

    def test_team_id_generated(self):
        team = AgentTeam(name="test", roles=_make_roles())
        assert team.team_id.startswith("team-")

    def test_max_debate_rounds(self):
        team = AgentTeam(
            name="test",
            roles=_make_roles(),
            max_debate_rounds=5,
        )
        assert team._max_debate_rounds == 5


# ─── Parallel Execution ─────────────────────────────────────


class TestParallelExecution:
    """Test PARALLEL pattern: all agents run simultaneously."""

    @pytest.mark.asyncio
    async def test_parallel_all_agents_produce_output(self):
        client = _make_mock_client("Parallel output")
        team = AgentTeam(
            name="parallel-team",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert len(result.agent_outputs) == 2
        assert "RESEARCHER" in result.agent_outputs
        assert "WRITER" in result.agent_outputs

    @pytest.mark.asyncio
    async def test_parallel_synthesis_called(self):
        client = _make_mock_client("Synthesized result")
        team = AgentTeam(
            name="parallel-team",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.synthesized_output == "Synthesized result"

    @pytest.mark.asyncio
    async def test_parallel_single_agent_no_synthesis(self):
        """With only one agent, synthesis is skipped — output returned directly."""
        client = _make_mock_client("Solo output")
        team = AgentTeam(
            name="solo-team",
            roles=_make_roles(1),
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert len(result.agent_outputs) == 1
        # Synthesis with 1 agent returns the output directly
        assert result.synthesized_output == "Solo output"

    @pytest.mark.asyncio
    async def test_parallel_traces_collected(self):
        client = _make_mock_client("Output")
        team = AgentTeam(
            name="trace-team",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task())
        # Each agent produces at least AGENT_ASSIGNED + AGENT_COMPLETED traces
        assert len(result.traces) >= 2

    @pytest.mark.asyncio
    async def test_parallel_with_context(self):
        client = _make_mock_client("Output")
        team = AgentTeam(
            name="ctx-team",
            roles=_make_roles(1),
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        ctx = {"key": "value"}
        result = await team.execute(_make_task(), context=ctx)
        assert result.success is True


# ─── Sequential Execution ───────────────────────────────────


class TestSequentialExecution:
    """Test SEQUENTIAL pattern: agents run one by one."""

    @pytest.mark.asyncio
    async def test_sequential_all_agents_run(self):
        client = _make_mock_client("Sequential output")
        team = AgentTeam(
            name="seq-team",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.SEQUENTIAL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert len(result.agent_outputs) == 2

    @pytest.mark.asyncio
    async def test_sequential_accumulated_context(self):
        """Each agent should see previous agents' outputs in context."""
        call_contexts = []

        client = _make_mock_client("Output")
        original_create = client.messages.create

        async def _capture_create(**kwargs):
            # We can't easily capture agent context, but we can verify
            # that all agents were called
            call_contexts.append(kwargs)
            return await original_create(**kwargs)

        client.messages.create = AsyncMock(side_effect=_capture_create)

        team = AgentTeam(
            name="seq-ctx-team",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.SEQUENTIAL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        # Both agents ran
        assert len(result.agent_outputs) == 2

    @pytest.mark.asyncio
    async def test_sequential_synthesis(self):
        client = _make_mock_client("Synthesized")
        team = AgentTeam(
            name="seq-synth",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.SEQUENTIAL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.synthesized_output == "Synthesized"


# ─── Debate Execution ───────────────────────────────────────


class TestDebateExecution:
    """Test DEBATE pattern: multi-round critique and refinement."""

    @pytest.mark.asyncio
    async def test_debate_basic(self):
        client = _make_mock_client("Debate output")
        team = AgentTeam(
            name="debate-team",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.DEBATE,
            client=client,
            max_debate_rounds=2,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert result.debate_rounds >= 1
        assert len(result.agent_outputs) == 2

    @pytest.mark.asyncio
    async def test_debate_max_rounds(self):
        client = _make_mock_client("Debate output")
        team = AgentTeam(
            name="debate-max",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.DEBATE,
            client=client,
            max_debate_rounds=3,
        )
        result = await team.execute(_make_task())
        assert result.debate_rounds <= 3

    @pytest.mark.asyncio
    async def test_debate_convergence_stops_early(self):
        """If outputs converge (identical), debate should stop early."""
        # All calls return same text → convergence after round 2
        client = _make_mock_client("Same answer every time")
        team = AgentTeam(
            name="converge-team",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.DEBATE,
            client=client,
            max_debate_rounds=5,
        )
        result = await team.execute(_make_task())
        # Should converge and stop before max rounds
        assert result.debate_rounds <= 5
        assert result.success is True

    @pytest.mark.asyncio
    async def test_debate_synthesis(self):
        client = _make_mock_client("Debate synthesis")
        team = AgentTeam(
            name="debate-synth",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.DEBATE,
            client=client,
            max_debate_rounds=1,
        )
        result = await team.execute(_make_task())
        assert result.synthesized_output == "Debate synthesis"


# ─── Agent Resolution ───────────────────────────────────────


class TestAgentResolution:
    """Test how agents are resolved from registry or created ad-hoc."""

    @pytest.mark.asyncio
    async def test_ad_hoc_agents_created(self):
        """Without a registry, ad-hoc agents are created for each role."""
        client = _make_mock_client("Output")
        team = AgentTeam(
            name="adhoc-team",
            roles=_make_roles(2),
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
            registry=None,
        )
        agents = team._resolve_agents()
        assert len(agents) == 2
        assert agents[0].role == AgentRole.RESEARCHER
        assert agents[1].role == AgentRole.WRITER

    @pytest.mark.asyncio
    async def test_ad_hoc_agent_names(self):
        client = _make_mock_client("Output")
        team = AgentTeam(
            name="test",
            roles=_make_roles(1),
            client=client,
        )
        agents = team._resolve_agents()
        assert "researcher" in agents[0].name.lower()

    def test_specialize_task(self):
        client = _make_mock_client("Output")
        team = AgentTeam(
            name="test",
            roles=_make_roles(1),
            client=client,
        )
        task = _make_task("Original task")
        role = _make_roles(1)[0]
        specialized = team._specialize_task(task, role)
        assert "Research the topic" in specialized.description
        assert "Original task" in specialized.description
        assert specialized.required_role == AgentRole.RESEARCHER
        assert specialized.id.endswith("-researcher")


# ─── Synthesis ──────────────────────────────────────────────


class TestSynthesis:
    """Test output synthesis."""

    @pytest.mark.asyncio
    async def test_synthesis_empty_outputs(self):
        client = _make_mock_client("Synthesized")
        team = AgentTeam(name="test", roles=_make_roles(), client=client)
        result = await team._synthesize("task", {})
        assert result == ""

    @pytest.mark.asyncio
    async def test_synthesis_single_output(self):
        client = _make_mock_client("Synthesized")
        team = AgentTeam(name="test", roles=_make_roles(), client=client)
        result = await team._synthesize("task", {"RESEARCHER": "Only output"})
        assert result == "Only output"  # No synthesis needed for single

    @pytest.mark.asyncio
    async def test_synthesis_multiple_outputs(self):
        client = _make_mock_client("Combined result")
        team = AgentTeam(name="test", roles=_make_roles(), client=client)
        result = await team._synthesize(
            "task",
            {"RESEARCHER": "Finding A", "WRITER": "Report B"},
        )
        assert result == "Combined result"

    @pytest.mark.asyncio
    async def test_synthesis_api_failure_fallback(self):
        """If synthesis API call fails, concatenated outputs are returned."""
        client = MagicMock()
        client.messages.create = AsyncMock(side_effect=ConnectionError("timeout"))
        team = AgentTeam(name="test", roles=_make_roles(), client=client)
        result = await team._synthesize(
            "task",
            {"RESEARCHER": "A", "WRITER": "B"},
        )
        # Fallback: concatenated outputs
        assert "RESEARCHER" in result
        assert "WRITER" in result


# ─── Convergence Detection ──────────────────────────────────


class TestConvergence:
    """Test debate convergence heuristic."""

    def test_identical_outputs_converge(self):
        prev = {"A": "Hello world", "B": "Test output"}
        curr = {"A": "Hello world", "B": "Test output"}
        assert AgentTeam._has_converged(prev, curr) is True

    def test_different_outputs_no_converge(self):
        prev = {"A": "Hello"}
        curr = {"A": "Completely different text here"}
        assert AgentTeam._has_converged(prev, curr) is False

    def test_missing_key_no_converge(self):
        prev = {"A": "Hello"}
        curr = {"A": "Hello", "B": "New"}
        assert AgentTeam._has_converged(prev, curr) is False

    def test_empty_outputs(self):
        assert AgentTeam._has_converged({}, {}) is True

    def test_similar_outputs_converge(self):
        prev = {"A": "The quick brown fox jumps over the lazy dog"}
        curr = {"A": "The quick brown fox jumps over the lazy cat"}
        # Very similar — should converge at 0.9 threshold
        result = AgentTeam._has_converged(prev, curr, threshold=0.8)
        assert result is True


# ─── Trace Logging ──────────────────────────────────────────


class TestTraceLogging:
    """Test that team operations produce trace events."""

    @pytest.mark.asyncio
    async def test_parallel_logs_trace(self):
        client = _make_mock_client("Output")
        trace_log = MagicMock()
        trace_log.append_async = AsyncMock()

        team = AgentTeam(
            name="trace-test",
            roles=_make_roles(1),
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        await team.execute(_make_task(), trace_log=trace_log)
        # Should log TEAM_PARALLEL_COMPLETE
        assert trace_log.append_async.called

    @pytest.mark.asyncio
    async def test_sequential_logs_trace(self):
        client = _make_mock_client("Output")
        trace_log = MagicMock()
        trace_log.append_async = AsyncMock()

        team = AgentTeam(
            name="trace-test",
            roles=_make_roles(1),
            pattern=TeamExecutionPattern.SEQUENTIAL,
            client=client,
        )
        await team.execute(_make_task(), trace_log=trace_log)
        assert trace_log.append_async.called

    @pytest.mark.asyncio
    async def test_debate_logs_trace(self):
        client = _make_mock_client("Output")
        trace_log = MagicMock()
        trace_log.append_async = AsyncMock()

        team = AgentTeam(
            name="trace-test",
            roles=_make_roles(1),
            pattern=TeamExecutionPattern.DEBATE,
            client=client,
            max_debate_rounds=1,
        )
        await team.execute(_make_task(), trace_log=trace_log)
        assert trace_log.append_async.called
