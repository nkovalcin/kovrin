"""
Kovrin Agent Registry

Central registry for all available agents. Supports registration,
lookup by role or capabilities, and default agent creation.
"""

import anthropic

from kovrin.agents.base import Agent, create_default_agents
from kovrin.core.models import AgentRole


class AgentRegistry:
    """Central registry for specialized agents with role and capability lookup."""

    def __init__(self, client: anthropic.AsyncAnthropic | None = None):
        self._agents: dict[str, Agent] = {}
        self._client = client

    def register(self, agent: Agent) -> None:
        """Register an agent in the registry."""
        self._agents[agent.name] = agent

    def unregister(self, name: str) -> None:
        """Remove an agent from the registry."""
        self._agents.pop(name, None)

    def get(self, name: str) -> Agent | None:
        """Get an agent by name."""
        return self._agents.get(name)

    def find_by_role(self, role: AgentRole) -> list[Agent]:
        """Find all agents with a specific role."""
        return [a for a in self._agents.values() if a.role == role]

    def find_by_capability(self, capability: str) -> list[Agent]:
        """Find all agents that have a specific capability."""
        return [a for a in self._agents.values() if capability in a.capabilities]

    def find_best(
        self, role: AgentRole | None = None, capabilities: list[str] | None = None
    ) -> Agent | None:
        """Find the best matching agent.

        Scoring: role match = 10 points, each capability match = 1 point.
        Returns the highest-scoring agent, or None if no agents exist.
        """
        if not self._agents:
            return None

        best_agent = None
        best_score = -1

        for agent in self._agents.values():
            score = 0
            if role and agent.role == role:
                score += 10
            if capabilities:
                score += sum(1 for c in capabilities if c in agent.capabilities)

            if score > best_score:
                best_score = score
                best_agent = agent

        return best_agent

    def register_defaults(self) -> None:
        """Register the default set of Kovrin agents."""
        for agent in create_default_agents(self._client):
            self.register(agent)

    @property
    def agents(self) -> list[Agent]:
        return list(self._agents.values())

    def __len__(self) -> int:
        return len(self._agents)
