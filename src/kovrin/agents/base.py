"""
Kovrin Specialized Agents

Each agent has a specific role (researcher, writer, reviewer, etc.)
with a tailored system prompt and capability set. Agents execute
sub-tasks via Claude API with role-specific expertise.

Agents can optionally use tools (calculator, datetime, etc.)
via Claude's tool_use feature.
"""

import anthropic

from kovrin.agents.tools import ToolExecutor, create_default_tools
from kovrin.core.models import AgentInfo, AgentRole, SubTask, Trace


# Role-specific system prompts
ROLE_PROMPTS: dict[AgentRole, str] = {
    AgentRole.RESEARCHER: (
        "You are a Research Agent. Your specialty is gathering, analyzing, and synthesizing information. "
        "You excel at: identifying patterns in data, evaluating sources, comparing alternatives, "
        "and producing thorough analytical summaries. Be methodical and cite your reasoning."
    ),
    AgentRole.WRITER: (
        "You are a Writer Agent. Your specialty is generating clear, well-structured content. "
        "You excel at: writing reports, proposals, documentation, summaries, and recommendations. "
        "Focus on clarity, actionability, and professional tone."
    ),
    AgentRole.REVIEWER: (
        "You are a Reviewer Agent. Your specialty is quality assurance and critical evaluation. "
        "You excel at: identifying gaps, inconsistencies, risks, and areas for improvement. "
        "Be constructive but thorough. Flag issues with specific evidence."
    ),
    AgentRole.PLANNER: (
        "You are a Planner Agent. Your specialty is strategic thinking and project organization. "
        "You excel at: breaking down complex goals, identifying dependencies, estimating effort, "
        "and creating actionable roadmaps. Think systematically."
    ),
    AgentRole.SPECIALIST: (
        "You are a Specialist Agent. You have deep domain expertise in the area relevant to this task. "
        "Apply your specialized knowledge to provide expert-level analysis and recommendations."
    ),
}

MAX_TOOL_ROUNDS = 10  # Max tool_use round-trips per execution


class Agent:
    """A specialized agent with a specific role and capabilities."""

    MODEL = "claude-sonnet-4-20250514"

    def __init__(
        self,
        name: str,
        role: AgentRole,
        capabilities: list[str] | None = None,
        system_prompt: str | None = None,
        client: anthropic.AsyncAnthropic | None = None,
        tools: ToolExecutor | None = None,
    ):
        self.name = name
        self.role = role
        self.capabilities = capabilities or []
        self.system_prompt = system_prompt or ROLE_PROMPTS.get(role, ROLE_PROMPTS[AgentRole.SPECIALIST])
        self._client = client or anthropic.AsyncAnthropic()
        self.tools = tools

    @property
    def info(self) -> AgentInfo:
        return AgentInfo(name=self.name, role=self.role, capabilities=self.capabilities)

    async def execute(self, subtask: SubTask, context: dict[str, str] | None = None) -> tuple[str, list[Trace]]:
        """Execute a sub-task with this agent's specialized perspective.

        If tools are available, the agent can make tool calls which are
        executed locally and fed back into the conversation.

        Returns (result_text, trace_events).
        """
        traces: list[Trace] = []

        traces.append(Trace(
            intent_id=subtask.parent_intent_id or "",
            task_id=subtask.id,
            event_type="AGENT_ASSIGNED",
            description=f"Agent '{self.name}' ({self.role.value}) assigned to: {subtask.description[:60]}",
            details={"agent": self.info.model_dump(), "tools": self.tools.tool_names if self.tools else []},
            risk_level=subtask.risk_level,
        ))

        dep_context = ""
        if context:
            dep_context = "\n\nPREVIOUS RESULTS:\n" + "\n".join(
                f"  [{tid}]: {result[:500]}" for tid, result in context.items()
            )

        messages = [{
            "role": "user",
            "content": f"TASK: {subtask.description}\n{dep_context}",
        }]

        # Build API call kwargs
        api_kwargs: dict = {
            "model": self.MODEL,
            "max_tokens": 4096,
            "system": self.system_prompt,
            "messages": messages,
        }

        # Add tools if available
        if self.tools and len(self.tools) > 0:
            api_kwargs["tools"] = self.tools.get_schemas()

        response = await self._client.messages.create(**api_kwargs)

        # Tool use loop
        rounds = 0
        while response.stop_reason == "tool_use" and self.tools and rounds < MAX_TOOL_ROUNDS:
            rounds += 1

            # Find all tool_use blocks in response
            tool_results = []
            for block in response.content:
                if block.type == "tool_use":
                    tool_result = await self.tools.execute(
                        name=block.name,
                        tool_input=block.input,
                        tool_use_id=block.id,
                    )
                    tool_results.append(tool_result)

                    traces.append(Trace(
                        intent_id=subtask.parent_intent_id or "",
                        task_id=subtask.id,
                        event_type="TOOL_CALL",
                        description=f"Tool '{block.name}' called by agent '{self.name}'",
                        details={
                            "tool": block.name,
                            "input": block.input,
                            "result": tool_result.content[:200],
                            "is_error": tool_result.is_error,
                        },
                    ))

            # Add assistant response + tool results to messages
            messages.append({"role": "assistant", "content": response.content})
            messages.append({
                "role": "user",
                "content": [
                    {
                        "type": "tool_result",
                        "tool_use_id": tr.tool_use_id,
                        "content": tr.content,
                        "is_error": tr.is_error,
                    }
                    for tr in tool_results
                ],
            })

            # Call API again with tool results
            api_kwargs["messages"] = messages
            response = await self._client.messages.create(**api_kwargs)

        # Extract final text
        result = ""
        for block in response.content:
            if hasattr(block, "text"):
                result += block.text

        traces.append(Trace(
            intent_id=subtask.parent_intent_id or "",
            task_id=subtask.id,
            event_type="AGENT_COMPLETED",
            description=f"Agent '{self.name}' completed: {subtask.description[:60]}",
            details={
                "agent": self.name,
                "output_length": len(result),
                "tool_rounds": rounds,
            },
            risk_level=subtask.risk_level,
        ))

        return result, traces


# Pre-built default agents
def create_default_agents(client: anthropic.AsyncAnthropic | None = None) -> list[Agent]:
    """Create the standard set of Kovrin agents with default tools."""
    default_tools = create_default_tools()
    return [
        Agent(
            name="Researcher",
            role=AgentRole.RESEARCHER,
            capabilities=["data_analysis", "pattern_recognition", "source_evaluation", "comparison"],
            client=client,
            tools=default_tools,
        ),
        Agent(
            name="Writer",
            role=AgentRole.WRITER,
            capabilities=["report_writing", "documentation", "summarization", "recommendations"],
            client=client,
            tools=default_tools,
        ),
        Agent(
            name="Reviewer",
            role=AgentRole.REVIEWER,
            capabilities=["quality_assurance", "risk_assessment", "gap_analysis", "validation"],
            client=client,
            tools=default_tools,
        ),
        Agent(
            name="Planner",
            role=AgentRole.PLANNER,
            capabilities=["strategic_planning", "roadmap_creation", "dependency_analysis", "estimation"],
            client=client,
            tools=default_tools,
        ),
    ]
