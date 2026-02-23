"""Tests for the LATTICE Multi-agent system.

Covers Agent, AgentRegistry, AgentCoordinator, and role inference.
"""

from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from kovrin.agents.base import Agent, ROLE_PROMPTS, create_default_agents
from kovrin.agents.coordinator import AgentCoordinator, _ROLE_KEYWORDS
from kovrin.agents.registry import AgentRegistry
from kovrin.core.models import AgentInfo, AgentRole, RiskLevel, SubTask, Trace


# ─── Agent ────────────────────────────────────────────────────

class TestAgent:
    def test_create_agent(self):
        agent = Agent(name="TestAgent", role=AgentRole.RESEARCHER)
        assert agent.name == "TestAgent"
        assert agent.role == AgentRole.RESEARCHER
        assert agent.capabilities == []

    def test_agent_with_capabilities(self):
        agent = Agent(
            name="Analyzer",
            role=AgentRole.RESEARCHER,
            capabilities=["data_analysis", "pattern_recognition"],
        )
        assert len(agent.capabilities) == 2
        assert "data_analysis" in agent.capabilities

    def test_agent_info(self):
        agent = Agent(
            name="Writer",
            role=AgentRole.WRITER,
            capabilities=["reports"],
        )
        info = agent.info
        assert isinstance(info, AgentInfo)
        assert info.name == "Writer"
        assert info.role == AgentRole.WRITER
        assert info.capabilities == ["reports"]

    def test_agent_default_system_prompt(self):
        for role in AgentRole:
            agent = Agent(name=f"test_{role.value}", role=role)
            assert agent.system_prompt  # Should have a prompt
            assert len(agent.system_prompt) > 20

    def test_agent_custom_system_prompt(self):
        agent = Agent(
            name="Custom",
            role=AgentRole.SPECIALIST,
            system_prompt="You are a custom specialist.",
        )
        assert agent.system_prompt == "You are a custom specialist."

    async def test_agent_execute(self):
        mock_client = AsyncMock()
        mock_response = MagicMock()
        mock_response.content = [MagicMock(text="Analysis complete: found 3 patterns")]
        mock_client.messages.create = AsyncMock(return_value=mock_response)

        agent = Agent(
            name="Researcher",
            role=AgentRole.RESEARCHER,
            client=mock_client,
        )

        task = SubTask(
            id="task-1",
            description="Analyze data",
            parent_intent_id="intent-1",
        )

        result, traces = await agent.execute(task)

        assert result == "Analysis complete: found 3 patterns"
        assert len(traces) == 2  # AGENT_ASSIGNED + AGENT_COMPLETED
        assert traces[0].event_type == "AGENT_ASSIGNED"
        assert traces[1].event_type == "AGENT_COMPLETED"

        mock_client.messages.create.assert_called_once()
        call_kwargs = mock_client.messages.create.call_args.kwargs
        assert call_kwargs["system"] == ROLE_PROMPTS[AgentRole.RESEARCHER]

    async def test_agent_execute_with_context(self):
        mock_client = AsyncMock()
        mock_response = MagicMock()
        mock_response.content = [MagicMock(text="Done")]
        mock_client.messages.create = AsyncMock(return_value=mock_response)

        agent = Agent(name="Writer", role=AgentRole.WRITER, client=mock_client)
        task = SubTask(id="task-2", description="Write report")

        context = {"task-1": "Previous analysis results"}
        result, traces = await agent.execute(task, context)

        call_kwargs = mock_client.messages.create.call_args.kwargs
        content = call_kwargs["messages"][0]["content"]
        assert "PREVIOUS RESULTS" in content
        assert "task-1" in content


# ─── Default Agents ───────────────────────────────────────────

class TestDefaultAgents:
    def test_create_default_agents(self):
        agents = create_default_agents()
        assert len(agents) == 4

    def test_default_agent_roles(self):
        agents = create_default_agents()
        roles = {a.role for a in agents}
        assert AgentRole.RESEARCHER in roles
        assert AgentRole.WRITER in roles
        assert AgentRole.REVIEWER in roles
        assert AgentRole.PLANNER in roles

    def test_default_agents_have_capabilities(self):
        agents = create_default_agents()
        for agent in agents:
            assert len(agent.capabilities) > 0


# ─── AgentRegistry ────────────────────────────────────────────

class TestAgentRegistry:
    def test_register_and_get(self):
        registry = AgentRegistry()
        agent = Agent(name="TestAgent", role=AgentRole.RESEARCHER)
        registry.register(agent)
        assert registry.get("TestAgent") is agent

    def test_get_nonexistent(self):
        registry = AgentRegistry()
        assert registry.get("Nonexistent") is None

    def test_unregister(self):
        registry = AgentRegistry()
        agent = Agent(name="TestAgent", role=AgentRole.RESEARCHER)
        registry.register(agent)
        registry.unregister("TestAgent")
        assert registry.get("TestAgent") is None

    def test_find_by_role(self):
        registry = AgentRegistry()
        r1 = Agent(name="R1", role=AgentRole.RESEARCHER)
        r2 = Agent(name="R2", role=AgentRole.RESEARCHER)
        w1 = Agent(name="W1", role=AgentRole.WRITER)
        registry.register(r1)
        registry.register(r2)
        registry.register(w1)

        researchers = registry.find_by_role(AgentRole.RESEARCHER)
        assert len(researchers) == 2
        assert all(a.role == AgentRole.RESEARCHER for a in researchers)

    def test_find_by_capability(self):
        registry = AgentRegistry()
        a1 = Agent(name="A1", role=AgentRole.RESEARCHER, capabilities=["data_analysis", "reports"])
        a2 = Agent(name="A2", role=AgentRole.WRITER, capabilities=["reports"])
        registry.register(a1)
        registry.register(a2)

        found = registry.find_by_capability("reports")
        assert len(found) == 2

        found = registry.find_by_capability("data_analysis")
        assert len(found) == 1

    def test_find_best_by_role(self):
        registry = AgentRegistry()
        r = Agent(name="R", role=AgentRole.RESEARCHER)
        w = Agent(name="W", role=AgentRole.WRITER)
        registry.register(r)
        registry.register(w)

        best = registry.find_best(role=AgentRole.RESEARCHER)
        assert best is r

    def test_find_best_by_capabilities(self):
        registry = AgentRegistry()
        a1 = Agent(name="A1", role=AgentRole.RESEARCHER, capabilities=["x", "y"])
        a2 = Agent(name="A2", role=AgentRole.RESEARCHER, capabilities=["x", "y", "z"])
        registry.register(a1)
        registry.register(a2)

        best = registry.find_best(capabilities=["x", "y", "z"])
        assert best is a2

    def test_find_best_empty_registry(self):
        registry = AgentRegistry()
        assert registry.find_best() is None

    def test_register_defaults(self):
        registry = AgentRegistry()
        registry.register_defaults()
        assert len(registry) == 4
        assert registry.get("Researcher") is not None
        assert registry.get("Writer") is not None
        assert registry.get("Reviewer") is not None
        assert registry.get("Planner") is not None

    def test_len(self):
        registry = AgentRegistry()
        assert len(registry) == 0
        registry.register(Agent(name="A", role=AgentRole.SPECIALIST))
        assert len(registry) == 1

    def test_agents_property(self):
        registry = AgentRegistry()
        a = Agent(name="A", role=AgentRole.SPECIALIST)
        registry.register(a)
        agents = registry.agents
        assert len(agents) == 1
        assert agents[0] is a


# ─── AgentCoordinator ────────────────────────────────────────

class TestAgentCoordinator:
    def _make_coordinator(self):
        registry = AgentRegistry()
        registry.register_defaults()
        return AgentCoordinator(registry), registry

    def test_assign_by_explicit_role(self):
        coord, reg = self._make_coordinator()
        task = SubTask(
            description="anything",
            required_role=AgentRole.WRITER,
        )
        agent = coord.assign(task)
        assert agent is not None
        assert agent.role == AgentRole.WRITER

    def test_assign_by_inferred_role_researcher(self):
        coord, _ = self._make_coordinator()
        task = SubTask(description="analyze data and investigate trends")
        agent = coord.assign(task)
        assert agent is not None
        assert agent.role == AgentRole.RESEARCHER

    def test_assign_by_inferred_role_writer(self):
        coord, _ = self._make_coordinator()
        task = SubTask(description="write a report and summarize findings")
        agent = coord.assign(task)
        assert agent is not None
        assert agent.role == AgentRole.WRITER

    def test_assign_by_inferred_role_reviewer(self):
        coord, _ = self._make_coordinator()
        task = SubTask(description="review the document and validate quality")
        agent = coord.assign(task)
        assert agent is not None
        assert agent.role == AgentRole.REVIEWER

    def test_assign_by_inferred_role_planner(self):
        coord, _ = self._make_coordinator()
        task = SubTask(description="plan the roadmap and organize priorities")
        agent = coord.assign(task)
        assert agent is not None
        assert agent.role == AgentRole.PLANNER

    def test_assign_fallback_to_best(self):
        coord, _ = self._make_coordinator()
        task = SubTask(description="do something generic and unrelated")
        agent = coord.assign(task)
        # Should still return an agent (best available)
        assert agent is not None

    def test_assign_empty_registry(self):
        registry = AgentRegistry()
        coord = AgentCoordinator(registry)
        task = SubTask(
            description="something",
            required_role=AgentRole.RESEARCHER,
        )
        agent = coord.assign(task)
        assert agent is None

    def test_infer_role_keywords(self):
        coord, _ = self._make_coordinator()
        # Test internal method
        assert coord._infer_role("analyze and research the data") == AgentRole.RESEARCHER
        assert coord._infer_role("write a comprehensive report") == AgentRole.WRITER
        assert coord._infer_role("review and validate quality") == AgentRole.REVIEWER
        assert coord._infer_role("plan the strategy and organize") == AgentRole.PLANNER

    def test_infer_role_no_match(self):
        coord, _ = self._make_coordinator()
        assert coord._infer_role("hello world") is None

    async def test_execute_with_agent(self):
        mock_client = AsyncMock()
        mock_response = MagicMock()
        mock_response.content = [MagicMock(text="Agent result")]
        mock_client.messages.create = AsyncMock(return_value=mock_response)

        registry = AgentRegistry(client=mock_client)
        registry.register_defaults()
        coord = AgentCoordinator(registry, client=mock_client)

        task = SubTask(
            description="analyze the expense data",
            required_role=AgentRole.RESEARCHER,
            parent_intent_id="intent-1",
        )

        result = await coord.execute_with_agent(task, {})
        assert result == "Agent result"

    async def test_execute_with_agent_fallback(self):
        """When no agent matches, uses fallback generic execution."""
        mock_client = AsyncMock()
        mock_response = MagicMock()
        mock_response.content = [MagicMock(text="Fallback result")]
        mock_client.messages.create = AsyncMock(return_value=mock_response)

        registry = AgentRegistry()  # Empty registry
        coord = AgentCoordinator(registry, client=mock_client)

        task = SubTask(description="something with no match")
        result = await coord.execute_with_agent(task, {})
        assert result == "Fallback result"

    async def test_execute_with_agent_no_client_no_agent_raises(self):
        registry = AgentRegistry()  # Empty
        coord = AgentCoordinator(registry, client=None)
        task = SubTask(description="something")

        with pytest.raises(RuntimeError, match="No agent available"):
            await coord.execute_with_agent(task, {})

    def test_create_trace_with_agent(self):
        agent = Agent(name="R", role=AgentRole.RESEARCHER)
        task = SubTask(id="task-1", description="test")
        trace = AgentCoordinator.create_trace(task, agent, "intent-1")
        assert trace.event_type == "AGENT_ASSIGNMENT"
        assert "R" in trace.description

    def test_create_trace_without_agent(self):
        task = SubTask(id="task-1", description="test")
        trace = AgentCoordinator.create_trace(task, None, "intent-1")
        assert "generic executor" in trace.description


# ─── Role Keywords Coverage ──────────────────────────────────

class TestRoleKeywords:
    def test_all_roles_have_keywords(self):
        for role in [AgentRole.RESEARCHER, AgentRole.WRITER, AgentRole.REVIEWER, AgentRole.PLANNER]:
            assert role in _ROLE_KEYWORDS
            assert len(_ROLE_KEYWORDS[role]) > 0

    def test_all_roles_have_prompts(self):
        for role in AgentRole:
            assert role in ROLE_PROMPTS
