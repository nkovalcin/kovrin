"""
Kovrin Agent Coordinator

Assigns sub-tasks to the most suitable specialized agent based on
the task's required role and description. Falls back to a generic
executor if no suitable agent is found.

Optionally integrates Delegation Capability Tokens (DCT) for
minimum-privilege agent delegation.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import anthropic

from kovrin.agents.base import Agent
from kovrin.agents.registry import AgentRegistry
from kovrin.core.models import AgentRole, DelegationScope, SubTask, Trace

if TYPE_CHECKING:
    from kovrin.engine.tokens import DelegationToken, TokenAuthority


# Keyword-to-role mapping for automatic role inference
_ROLE_KEYWORDS: dict[AgentRole, list[str]] = {
    AgentRole.RESEARCHER: [
        "analyze",
        "research",
        "investigate",
        "compare",
        "evaluate",
        "assess",
        "audit",
        "review data",
        "identify patterns",
    ],
    AgentRole.WRITER: [
        "write",
        "generate",
        "create",
        "draft",
        "compose",
        "summarize",
        "document",
        "report",
        "recommend",
    ],
    AgentRole.REVIEWER: [
        "review",
        "validate",
        "check",
        "verify",
        "quality",
        "inspect",
        "test",
        "ensure",
    ],
    AgentRole.PLANNER: [
        "plan",
        "schedule",
        "roadmap",
        "strategy",
        "organize",
        "prioritize",
        "decompose",
        "coordinate",
    ],
}


class AgentCoordinator:
    """Coordinates task assignment across specialized agents."""

    def __init__(
        self,
        registry: AgentRegistry,
        client: anthropic.AsyncAnthropic | None = None,
        token_authority: TokenAuthority | None = None,
    ):
        self._registry = registry
        self._client = client
        self._token_authority = token_authority
        self._active_tokens: dict[str, DelegationToken] = {}  # task_id -> token
        self._fallback_agent: Agent | None = None

    def assign(self, subtask: SubTask) -> Agent | None:
        """Assign the best agent for a sub-task.

        Priority:
        1. Use required_role if specified on the task
        2. Infer role from task description keywords
        3. Fall back to best available agent

        If token_authority is set, issues a DCT for the assigned agent.
        """
        agent: Agent | None = None

        # 1. Explicit role
        if subtask.required_role:
            agents = self._registry.find_by_role(subtask.required_role)
            if agents:
                agent = agents[0]

        # 2. Infer from description
        if not agent:
            inferred_role = self._infer_role(subtask.description)
            if inferred_role:
                agents = self._registry.find_by_role(inferred_role)
                if agents:
                    agent = agents[0]

        # 3. Best match by capabilities
        if not agent:
            agent = self._registry.find_best()

        # Issue delegation token if authority is set
        if agent and self._token_authority:
            scope = DelegationScope(
                allowed_risk_levels=[subtask.risk_level],
                max_tasks=1,
                max_depth=1,
            )
            token = self._token_authority.issue(agent.name, scope)
            self._active_tokens[subtask.id] = token

        return agent

    def _infer_role(self, description: str) -> AgentRole | None:
        """Infer the most suitable role from task description."""
        desc_lower = description.lower()
        best_role = None
        best_score = 0

        for role, keywords in _ROLE_KEYWORDS.items():
            score = sum(1 for kw in keywords if kw in desc_lower)
            if score > best_score:
                best_score = score
                best_role = role

        return best_role if best_score > 0 else None

    async def execute_with_agent(
        self,
        subtask: SubTask,
        dep_results: dict[str, str],
    ) -> str:
        """Assign and execute a task with the appropriate agent.

        Compatible with GraphExecutor's execute_fn signature:
        async (SubTask, dict[str, str]) -> str

        If token_authority is set, validates the DCT before execution.
        """
        agent = self.assign(subtask)

        # Validate delegation token if present
        if agent and self._token_authority and subtask.id in self._active_tokens:
            token = self._active_tokens[subtask.id]
            valid, reason = self._token_authority.validate(token)
            if not valid:
                raise RuntimeError(f"DCT validation failed for {agent.name}: {reason}")
            scope_ok, scope_reason = self._token_authority.check_scope(token, subtask)
            if not scope_ok:
                raise RuntimeError(f"DCT scope violation for {agent.name}: {scope_reason}")
            self._token_authority.record_execution(token)

        if agent:
            result, traces = await agent.execute(subtask, dep_results)
            return result

        # No agent found — use fallback generic execution
        if self._client:
            response = await self._client.messages.create(
                model="claude-sonnet-4-20250514",
                max_tokens=4096,
                messages=[
                    {
                        "role": "user",
                        "content": f"Execute this task:\n{subtask.description}",
                    }
                ],
            )
            return response.content[0].text

        raise RuntimeError(f"No agent available for task: {subtask.description[:60]}")

    @staticmethod
    def create_trace(subtask: SubTask, agent: Agent | None, intent_id: str) -> Trace:
        """Create a trace event for agent assignment."""
        if agent:
            return Trace(
                intent_id=intent_id,
                task_id=subtask.id,
                event_type="AGENT_ASSIGNMENT",
                description=f"Assigned to {agent.name} ({agent.role.value}): {subtask.description[:50]}",
                details={"agent": agent.info.model_dump()},
                risk_level=subtask.risk_level,
            )
        return Trace(
            intent_id=intent_id,
            task_id=subtask.id,
            event_type="AGENT_ASSIGNMENT",
            description=f"No specialized agent — using generic executor: {subtask.description[:50]}",
            risk_level=subtask.risk_level,
        )
