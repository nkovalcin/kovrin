"""
Agent Team — Multi-Agent Collaborative Execution

A group of agents working together on a shared goal with three
execution patterns:
  - PARALLEL: all agents execute simultaneously, results synthesized
  - SEQUENTIAL: agents run one by one, each sees previous outputs
  - DEBATE: multi-round debate where agents critique each other

Integrates with the existing AgentRegistry and AgentCoordinator
for agent lookup and DCT token issuance.
"""

from __future__ import annotations

import asyncio
import logging
import uuid
from typing import TYPE_CHECKING

import anthropic

from kovrin.agents.base import Agent, ROLE_PROMPTS
from kovrin.core.models import (
    AgentRole,
    DEFAULT_MODEL_ROUTING,
    SubTask,
    TeamExecutionPattern,
    TeamResult,
    TeamRole,
    Trace,
)

if TYPE_CHECKING:
    from kovrin.agents.coordinator import AgentCoordinator
    from kovrin.agents.registry import AgentRegistry
    from kovrin.audit.trace_logger import ImmutableTraceLog

logger = logging.getLogger(__name__)


class AgentTeam:
    """A group of agents working together on a shared goal.

    Execution patterns:
      - **PARALLEL**: All agents execute simultaneously on the same task.
        Each gets the same base context.  Results are synthesized at the end.
      - **SEQUENTIAL**: Agents execute one by one.  Each agent sees the
        base context plus all previous agents' outputs.
      - **DEBATE**: Multi-round debate.  Round 1: all agents produce initial
        output.  Round 2+: each agent sees others' outputs and can revise.
        Continues for ``max_debate_rounds`` or until outputs converge.

    Example::

        team = AgentTeam(
            name="research-team",
            roles=[
                TeamRole(agent_role=AgentRole.RESEARCHER, task_description="Gather data"),
                TeamRole(agent_role=AgentRole.REVIEWER, task_description="Evaluate findings"),
            ],
            pattern=TeamExecutionPattern.PARALLEL,
        )
        result = await team.execute(subtask)
        print(result.synthesized_output)
    """

    def __init__(
        self,
        name: str,
        roles: list[TeamRole],
        pattern: TeamExecutionPattern = TeamExecutionPattern.PARALLEL,
        registry: AgentRegistry | None = None,
        coordinator: AgentCoordinator | None = None,
        client: anthropic.AsyncAnthropic | None = None,
        max_debate_rounds: int = 3,
        synthesizer_model: str | None = None,
    ) -> None:
        self._name = name
        self._roles = roles
        self._pattern = pattern
        self._registry = registry
        self._coordinator = coordinator
        self._client = client or anthropic.AsyncAnthropic()
        self._max_debate_rounds = max_debate_rounds
        self._synthesizer_model = (
            synthesizer_model or DEFAULT_MODEL_ROUTING["task_executor"].value
        )
        self._team_id = f"team-{uuid.uuid4().hex[:8]}"

    @property
    def team_id(self) -> str:
        return self._team_id

    async def execute(
        self,
        task: SubTask,
        context: dict[str, str] | None = None,
        trace_log: ImmutableTraceLog | None = None,
    ) -> TeamResult:
        """Execute the team on a task using the configured pattern."""
        from kovrin.observability.tracing import get_tracer

        tracer = get_tracer()
        with tracer.start_as_current_span("kovrin.team") as span:
            span.set_attribute("kovrin.team_id", self._team_id)
            span.set_attribute("kovrin.team_name", self._name)
            span.set_attribute("kovrin.team_pattern", self._pattern.value)
            span.set_attribute("kovrin.team_roles", len(self._roles))

            match self._pattern:
                case TeamExecutionPattern.PARALLEL:
                    result = await self._execute_parallel(task, context, trace_log)
                case TeamExecutionPattern.SEQUENTIAL:
                    result = await self._execute_sequential(task, context, trace_log)
                case TeamExecutionPattern.DEBATE:
                    result = await self._execute_debate(task, context, trace_log)

            span.set_attribute("kovrin.team_success", result.success)
            return result

    # ── Execution patterns ───────────────────────────────────

    async def _execute_parallel(
        self,
        task: SubTask,
        context: dict[str, str] | None,
        trace_log: ImmutableTraceLog | None,
    ) -> TeamResult:
        """All agents execute simultaneously; results synthesized."""
        agents = self._resolve_agents()
        all_traces: list[Trace] = []
        agent_outputs: dict[str, str] = {}

        async def _run_agent(role: TeamRole, agent: Agent) -> tuple[str, str, list[Trace]]:
            specialized = self._specialize_task(task, role)
            result_text, traces = await agent.execute(specialized, context)
            return role.agent_role.value, result_text, traces

        tasks = [
            _run_agent(role, agent)
            for role, agent in zip(self._roles, agents)
        ]
        results = await asyncio.gather(*tasks, return_exceptions=True)

        for res in results:
            if isinstance(res, Exception):
                logger.error("Agent failed: %s", res)
                continue
            role_name, output, traces = res
            agent_outputs[role_name] = output
            all_traces.extend(traces)

        synthesized = await self._synthesize(task.description, agent_outputs)

        if trace_log is not None:
            await trace_log.append_async(
                Trace(
                    intent_id=task.parent_intent_id or "",
                    task_id=task.id,
                    event_type="TEAM_PARALLEL_COMPLETE",
                    description=f"Team '{self._name}' parallel execution: {len(agent_outputs)} agents",
                    details={
                        "team_id": self._team_id,
                        "agents": list(agent_outputs.keys()),
                    },
                )
            )

        return TeamResult(
            team_id=self._team_id,
            pattern=self._pattern,
            agent_outputs=agent_outputs,
            synthesized_output=synthesized,
            traces=all_traces,
            success=len(agent_outputs) > 0,
        )

    async def _execute_sequential(
        self,
        task: SubTask,
        context: dict[str, str] | None,
        trace_log: ImmutableTraceLog | None,
    ) -> TeamResult:
        """Agents execute one by one, each seeing previous outputs."""
        agents = self._resolve_agents()
        all_traces: list[Trace] = []
        agent_outputs: dict[str, str] = {}
        accumulated_context = dict(context or {})

        for role, agent in zip(self._roles, agents):
            specialized = self._specialize_task(task, role)
            result_text, traces = await agent.execute(specialized, accumulated_context)
            agent_outputs[role.agent_role.value] = result_text
            all_traces.extend(traces)

            # Each subsequent agent sees all previous outputs
            accumulated_context[f"output_{role.agent_role.value.lower()}"] = result_text

        synthesized = await self._synthesize(task.description, agent_outputs)

        if trace_log is not None:
            await trace_log.append_async(
                Trace(
                    intent_id=task.parent_intent_id or "",
                    task_id=task.id,
                    event_type="TEAM_SEQUENTIAL_COMPLETE",
                    description=f"Team '{self._name}' sequential execution: {len(agent_outputs)} agents",
                    details={
                        "team_id": self._team_id,
                        "agents": list(agent_outputs.keys()),
                    },
                )
            )

        return TeamResult(
            team_id=self._team_id,
            pattern=self._pattern,
            agent_outputs=agent_outputs,
            synthesized_output=synthesized,
            traces=all_traces,
            success=len(agent_outputs) > 0,
        )

    async def _execute_debate(
        self,
        task: SubTask,
        context: dict[str, str] | None,
        trace_log: ImmutableTraceLog | None,
    ) -> TeamResult:
        """Multi-round debate: agents critique and refine each other's outputs."""
        agents = self._resolve_agents()
        all_traces: list[Trace] = []
        current_outputs: dict[str, str] = {}
        rounds_completed = 0

        for round_num in range(self._max_debate_rounds):
            previous_outputs = dict(current_outputs)
            round_context = dict(context or {})

            # Inject other agents' outputs from previous round
            if previous_outputs:
                round_context["debate_round"] = str(round_num + 1)
                round_context["other_agent_outputs"] = "\n\n---\n\n".join(
                    f"**{name}**: {output}"
                    for name, output in previous_outputs.items()
                )

            for role, agent in zip(self._roles, agents):
                # In debate, each agent's prompt includes others' outputs
                specialized = self._specialize_task(task, role)
                if round_num > 0:
                    specialized = SubTask(
                        id=f"{task.id}-{role.agent_role.value.lower()}-r{round_num}",
                        description=(
                            f"{role.task_description}\n\n"
                            f"Original task: {task.description}\n\n"
                            f"This is debate round {round_num + 1}. "
                            f"Review and improve upon the other agents' perspectives:\n\n"
                            + "\n\n".join(
                                f"**{n}**: {o[:500]}"
                                for n, o in previous_outputs.items()
                                if n != role.agent_role.value
                            )
                        ),
                        risk_level=task.risk_level,
                        speculation_tier=task.speculation_tier,
                        parent_intent_id=task.parent_intent_id,
                        required_role=role.agent_role,
                    )

                result_text, traces = await agent.execute(specialized, round_context)
                current_outputs[role.agent_role.value] = result_text
                all_traces.extend(traces)

            rounds_completed = round_num + 1

            # Check for convergence: if outputs haven't changed meaningfully, stop
            if previous_outputs and self._has_converged(previous_outputs, current_outputs):
                logger.info(
                    "Team %s debate converged after %d rounds",
                    self._name,
                    rounds_completed,
                )
                break

        synthesized = await self._synthesize(task.description, current_outputs)

        if trace_log is not None:
            await trace_log.append_async(
                Trace(
                    intent_id=task.parent_intent_id or "",
                    task_id=task.id,
                    event_type="TEAM_DEBATE_COMPLETE",
                    description=(
                        f"Team '{self._name}' debate: {rounds_completed} rounds, "
                        f"{len(current_outputs)} agents"
                    ),
                    details={
                        "team_id": self._team_id,
                        "rounds": rounds_completed,
                        "agents": list(current_outputs.keys()),
                    },
                )
            )

        return TeamResult(
            team_id=self._team_id,
            pattern=self._pattern,
            agent_outputs=current_outputs,
            synthesized_output=synthesized,
            debate_rounds=rounds_completed,
            traces=all_traces,
            success=len(current_outputs) > 0,
        )

    # ── Helpers ──────────────────────────────────────────────

    async def _synthesize(
        self, task_description: str, agent_outputs: dict[str, str]
    ) -> str:
        """Use Claude to synthesize multiple agent outputs into one result."""
        if not agent_outputs:
            return ""

        if len(agent_outputs) == 1:
            return next(iter(agent_outputs.values()))

        outputs_text = "\n\n---\n\n".join(
            f"## {agent_name} Output:\n{output}"
            for agent_name, output in agent_outputs.items()
        )

        try:
            response = await self._client.messages.create(
                model=self._synthesizer_model,
                max_tokens=4096,
                messages=[
                    {
                        "role": "user",
                        "content": (
                            "Synthesize these multiple agent outputs into one coherent result.\n\n"
                            f"TASK: {task_description}\n\n"
                            f"AGENT OUTPUTS:\n{outputs_text}\n\n"
                            "Produce a single, unified result that captures the best insights "
                            "from all agents. Remove redundancy. Resolve contradictions. "
                            "Be comprehensive yet concise."
                        ),
                    }
                ],
            )
            return response.content[0].text
        except Exception as exc:
            logger.error("Synthesis failed: %s — returning concatenated outputs", exc)
            return outputs_text

    def _resolve_agents(self) -> list[Agent]:
        """Resolve agents from registry or create ad-hoc agents for each role."""
        agents: list[Agent] = []
        for role in self._roles:
            if self._registry:
                found = self._registry.find_by_role(role.agent_role)
                if found:
                    agents.append(found[0])
                    continue

            # Create ad-hoc agent for this role
            agents.append(
                Agent(
                    name=f"{role.agent_role.value.lower()}-{self._team_id[:8]}",
                    role=role.agent_role,
                    system_prompt=role.custom_prompt or ROLE_PROMPTS.get(role.agent_role),
                    client=self._client,
                )
            )
        return agents

    def _specialize_task(self, task: SubTask, role: TeamRole) -> SubTask:
        """Create a task copy with role-specific description."""
        return SubTask(
            id=f"{task.id}-{role.agent_role.value.lower()}",
            description=f"{role.task_description}\n\nOriginal task: {task.description}",
            risk_level=task.risk_level,
            speculation_tier=task.speculation_tier,
            parent_intent_id=task.parent_intent_id,
            required_role=role.agent_role,
        )

    @staticmethod
    def _has_converged(
        prev: dict[str, str],
        curr: dict[str, str],
        threshold: float = 0.9,
    ) -> bool:
        """Check if debate outputs have converged (simple length-similarity heuristic)."""
        if set(prev.keys()) != set(curr.keys()):
            return False

        similarities: list[float] = []
        for key in prev:
            p, c = prev[key], curr[key]
            if not p or not c:
                similarities.append(0.0)
                continue
            # Simple overlap metric: shared character count / max length
            common = sum(1 for a, b in zip(p, c) if a == b)
            similarities.append(common / max(len(p), len(c)))

        if not similarities:
            return True  # Both empty → converged
        avg = sum(similarities) / len(similarities)
        return avg >= threshold
