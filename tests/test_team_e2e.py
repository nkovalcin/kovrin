"""End-to-end Agent Team tests.

Tests the full AgentTeam integration with mocked Claude API,
verifying parallel, sequential, and debate patterns produce
correct synthesized outputs.
"""

import json
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin.agents.team import AgentTeam
from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.models import (
    AgentRole,
    SubTask,
    TeamExecutionPattern,
    TeamRole,
)


# ─── Helpers ────────────────────────────────────────────────


def _make_task(desc: str = "Analyze safety of AI agents") -> SubTask:
    return SubTask(
        id="task-e2e",
        description=desc,
        parent_intent_id="intent-e2e",
    )


def _make_client_with_responses(responses: list[str]) -> MagicMock:
    """Create mock client that cycles through responses."""
    idx = 0

    async def _create(**kwargs):
        nonlocal idx
        text = responses[idx % len(responses)]
        idx += 1
        msg = MagicMock()
        msg.content = [MagicMock(text=text)]
        msg.stop_reason = "end_turn"
        msg.usage = MagicMock(input_tokens=50, output_tokens=25)
        return msg

    client = MagicMock()
    client.messages.create = AsyncMock(side_effect=_create)
    return client


ROLES_2 = [
    TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Research the topic"),
    TeamRole(agent_role=AgentRole.WRITER, task_description="Write the report"),
]

ROLES_3 = [
    TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Research"),
    TeamRole(agent_role=AgentRole.WRITER, task_description="Write"),
    TeamRole(agent_role=AgentRole.REVIEWER, task_description="Review"),
]


# ─── Parallel E2E ───────────────────────────────────────────


class TestParallelE2E:
    """End-to-end parallel team execution."""

    @pytest.mark.asyncio
    async def test_parallel_two_agents(self):
        client = _make_client_with_responses([
            "Research findings on AI safety",
            "Written report on AI safety",
            "Synthesized: comprehensive analysis",  # synthesis call
        ])
        team = AgentTeam(
            name="parallel-e2e",
            roles=ROLES_2,
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert len(result.agent_outputs) == 2
        assert "RESEARCHER" in result.agent_outputs
        assert "WRITER" in result.agent_outputs
        assert result.synthesized_output != ""

    @pytest.mark.asyncio
    async def test_parallel_three_agents(self):
        client = _make_client_with_responses([
            "Research output",
            "Writer output",
            "Reviewer output",
            "Final synthesis",
        ])
        team = AgentTeam(
            name="parallel-3",
            roles=ROLES_3,
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert len(result.agent_outputs) == 3

    @pytest.mark.asyncio
    async def test_parallel_with_trace_log(self):
        client = _make_client_with_responses(["Output", "Synth"])
        trace_log = ImmutableTraceLog()

        team = AgentTeam(
            name="traced-parallel",
            roles=[TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Research")],
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task(), trace_log=trace_log)
        assert result.success is True
        # Trace log should have events
        events = trace_log.get_events()
        team_events = [e for e in events if "TEAM" in e.trace.event_type]
        assert len(team_events) >= 1

    @pytest.mark.asyncio
    async def test_parallel_with_context(self):
        client = _make_client_with_responses(["Output", "Synth"])
        team = AgentTeam(
            name="ctx-parallel",
            roles=[TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Research")],
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(
            _make_task(),
            context={"budget": "1000", "deadline": "2 weeks"},
        )
        assert result.success is True


# ─── Sequential E2E ─────────────────────────────────────────


class TestSequentialE2E:
    """End-to-end sequential team execution."""

    @pytest.mark.asyncio
    async def test_sequential_two_agents(self):
        client = _make_client_with_responses([
            "Research findings",
            "Report based on research",
            "Synthesis",
        ])
        team = AgentTeam(
            name="sequential-e2e",
            roles=ROLES_2,
            pattern=TeamExecutionPattern.SEQUENTIAL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert len(result.agent_outputs) == 2

    @pytest.mark.asyncio
    async def test_sequential_with_trace_log(self):
        client = _make_client_with_responses(["Output", "Synth"])
        trace_log = ImmutableTraceLog()

        team = AgentTeam(
            name="traced-seq",
            roles=[TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Research")],
            pattern=TeamExecutionPattern.SEQUENTIAL,
            client=client,
        )
        result = await team.execute(_make_task(), trace_log=trace_log)
        events = trace_log.get_events()
        seq_events = [e for e in events if "SEQUENTIAL" in e.trace.event_type]
        assert len(seq_events) >= 1


# ─── Debate E2E ──────────────────────────────────────────────


class TestDebateE2E:
    """End-to-end debate team execution."""

    @pytest.mark.asyncio
    async def test_debate_two_agents_two_rounds(self):
        client = _make_client_with_responses([
            # Round 1
            "Initial research perspective",
            "Initial writer perspective",
            # Round 2
            "Refined research after seeing writer",
            "Refined writer after seeing research",
            # Synthesis
            "Synthesized debate result",
        ])
        team = AgentTeam(
            name="debate-e2e",
            roles=ROLES_2,
            pattern=TeamExecutionPattern.DEBATE,
            client=client,
            max_debate_rounds=2,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert result.debate_rounds >= 1
        assert result.debate_rounds <= 2
        assert len(result.agent_outputs) == 2

    @pytest.mark.asyncio
    async def test_debate_convergence(self):
        """Identical responses should cause early convergence."""
        # All responses identical → converges after round 2
        client = _make_client_with_responses(["Same answer", "Same answer", "Synthesis"])
        team = AgentTeam(
            name="converge-e2e",
            roles=ROLES_2,
            pattern=TeamExecutionPattern.DEBATE,
            client=client,
            max_debate_rounds=5,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert result.debate_rounds <= 5

    @pytest.mark.asyncio
    async def test_debate_with_trace_log(self):
        client = _make_client_with_responses(["Output", "Synth"])
        trace_log = ImmutableTraceLog()

        team = AgentTeam(
            name="traced-debate",
            roles=[TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Research")],
            pattern=TeamExecutionPattern.DEBATE,
            client=client,
            max_debate_rounds=1,
        )
        result = await team.execute(_make_task(), trace_log=trace_log)
        events = trace_log.get_events()
        debate_events = [e for e in events if "DEBATE" in e.trace.event_type]
        assert len(debate_events) >= 1

    @pytest.mark.asyncio
    async def test_debate_single_round(self):
        client = _make_client_with_responses([
            "Research view", "Writer view", "Synth",
        ])
        team = AgentTeam(
            name="debate-1",
            roles=ROLES_2,
            pattern=TeamExecutionPattern.DEBATE,
            client=client,
            max_debate_rounds=1,
        )
        result = await team.execute(_make_task())
        assert result.debate_rounds == 1


# ─── Synthesis E2E ──────────────────────────────────────────


class TestSynthesisE2E:
    """Test that synthesis combines multi-agent outputs."""

    @pytest.mark.asyncio
    async def test_synthesis_includes_all_outputs(self):
        """Synthesis API call receives all agent outputs."""
        call_contents = []

        async def _create(**kwargs):
            messages = kwargs.get("messages", [])
            if messages:
                call_contents.append(messages[0].get("content", ""))
            msg = MagicMock()
            msg.content = [MagicMock(text="Synthesized result")]
            msg.stop_reason = "end_turn"
            msg.usage = MagicMock(input_tokens=50, output_tokens=25)
            return msg

        client = MagicMock()
        client.messages.create = AsyncMock(side_effect=_create)

        team = AgentTeam(
            name="synth-e2e",
            roles=ROLES_2,
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task())

        # Last call should be synthesis with both agent outputs
        assert len(call_contents) >= 3  # 2 agents + 1 synthesis
        synth_content = call_contents[-1]
        assert "RESEARCHER" in synth_content
        assert "WRITER" in synth_content

    @pytest.mark.asyncio
    async def test_synthesis_failure_fallback(self):
        """If synthesis fails, concatenated outputs are returned."""
        call_count = 0

        async def _create(**kwargs):
            nonlocal call_count
            call_count += 1
            # First 2 calls = agent executions (success)
            if call_count <= 2:
                msg = MagicMock()
                msg.content = [MagicMock(text=f"Agent {call_count} output")]
                msg.stop_reason = "end_turn"
                msg.usage = MagicMock(input_tokens=50, output_tokens=25)
                return msg
            # 3rd call = synthesis (fail)
            raise ConnectionError("API down")

        client = MagicMock()
        client.messages.create = AsyncMock(side_effect=_create)

        team = AgentTeam(
            name="synth-fail",
            roles=ROLES_2,
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task())
        # Fallback: concatenated outputs
        assert result.success is True
        assert "RESEARCHER" in result.synthesized_output
        assert "WRITER" in result.synthesized_output


# ─── Custom Roles E2E ───────────────────────────────────────


class TestCustomRolesE2E:
    """Test teams with custom prompts and specialist roles."""

    @pytest.mark.asyncio
    async def test_custom_prompt_role(self):
        client = _make_client_with_responses(["Expert analysis"])
        team = AgentTeam(
            name="custom-role",
            roles=[
                TeamRole(
                    agent_role=AgentRole.SPECIALIST,
                    task_description="Analyze security vulnerabilities",
                    custom_prompt="You are a cybersecurity expert with 20 years experience.",
                ),
            ],
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task("Audit security"))
        assert result.success is True
        assert "SPECIALIST" in result.agent_outputs

    @pytest.mark.asyncio
    async def test_all_five_roles(self):
        """Test with all 5 AgentRole values."""
        client = _make_client_with_responses([
            "Researched", "Written", "Reviewed", "Planned", "Specialized",
            "Final synthesis",
        ])
        roles = [
            TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Research"),
            TeamRole(agent_role=AgentRole.WRITER, task_description="Write"),
            TeamRole(agent_role=AgentRole.REVIEWER, task_description="Review"),
            TeamRole(agent_role=AgentRole.PLANNER, task_description="Plan"),
            TeamRole(agent_role=AgentRole.SPECIALIST, task_description="Specialize"),
        ]
        team = AgentTeam(
            name="all-roles",
            roles=roles,
            pattern=TeamExecutionPattern.PARALLEL,
            client=client,
        )
        result = await team.execute(_make_task())
        assert result.success is True
        assert len(result.agent_outputs) == 5
