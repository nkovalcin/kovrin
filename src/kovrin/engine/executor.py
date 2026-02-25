"""
Kovrin Task Executor

Executes individual sub-tasks via Claude API. Each execution
generates immutable trace events for the audit log.

The executor integrates with the risk router to handle
different routing decisions:
- AUTO_EXECUTE: execute immediately
- SANDBOX_REVIEW: execute with enhanced logging (MVP)
- HUMAN_APPROVAL: request approval before execution

When tools are enabled, the executor supports Claude's tool_use
feature with safety-gated execution through SafeToolRouter.
Every tool call is validated against the safety pipeline before
execution.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

import anthropic

from kovrin.core.models import (
    ApprovalRequest,
    AutonomySettings,
    DEFAULT_MODEL_ROUTING,
    RoutingAction,
    SubTask,
    TaskStatus,
    Trace,
)
from kovrin.engine.risk_router import RiskRouter

if TYPE_CHECKING:
    import asyncio

    from kovrin.engine.prm import ProcessRewardModel
    from kovrin.tools.registry import ToolRegistry
    from kovrin.tools.router import SafeToolRouter

MAX_TOOL_ROUNDS = 10  # Max tool_use round-trips per execution


class TaskExecutor:
    """Executes sub-tasks via Claude API with risk-aware routing.

    When tool_registry and tool_router are provided, agents can
    use tools (code execution, web search, file ops, etc.) with
    every tool call validated through the Kovrin safety pipeline.
    """

    MODEL = DEFAULT_MODEL_ROUTING["task_executor"].value

    def __init__(
        self,
        client: anthropic.AsyncAnthropic | None = None,
        risk_router: RiskRouter | None = None,
        approval_callback: Callable[[ApprovalRequest], asyncio.Future[bool]] | None = None,
        autonomy_settings: AutonomySettings | None = None,
        prm: ProcessRewardModel | None = None,
        tool_registry: ToolRegistry | None = None,
        tool_router: SafeToolRouter | None = None,
        model: str | None = None,
    ):
        self._client = client or anthropic.AsyncAnthropic()
        self._router = risk_router or RiskRouter()
        self._model = model or self.MODEL
        self._approval_callback = approval_callback
        self._autonomy_settings = autonomy_settings
        self._prm = prm
        self._tool_registry = tool_registry
        self._tool_router = tool_router

    def update_autonomy_settings(self, settings: AutonomySettings | None) -> None:
        """Update autonomy settings at runtime."""
        self._autonomy_settings = settings

    async def execute(
        self,
        subtask: SubTask,
        dep_results: dict[str, str] | None = None,
        intent_context: str = "",
    ) -> tuple[str, list[Trace]]:
        """Execute a single sub-task.

        Returns (result_text, trace_events).
        """
        traces: list[Trace] = []

        # Route the task
        decision = self._router.route(subtask, self._autonomy_settings)
        traces.append(RiskRouter.create_trace(subtask, decision, subtask.parent_intent_id or ""))

        # Handle routing decision
        if decision.action == RoutingAction.HUMAN_APPROVAL:
            approved = await self._router.request_human_approval(
                subtask, decision, approval_callback=self._approval_callback
            )
            if not approved:
                subtask.status = TaskStatus.AWAITING_HUMAN
                traces.append(
                    Trace(
                        intent_id=subtask.parent_intent_id or "",
                        task_id=subtask.id,
                        event_type="HUMAN_REJECTED",
                        description=f"Human rejected: {subtask.description[:60]}",
                        risk_level=subtask.risk_level,
                    )
                )
                raise RuntimeError(f"Human rejected task: {subtask.description[:80]}")

            traces.append(
                Trace(
                    intent_id=subtask.parent_intent_id or "",
                    task_id=subtask.id,
                    event_type="HUMAN_APPROVED",
                    description=f"Human approved: {subtask.description[:60]}",
                    risk_level=subtask.risk_level,
                )
            )

        # Build execution prompt
        dep_context = ""
        if dep_results:
            dep_context = "\n\nRESULTS FROM PREVIOUS TASKS:\n" + "\n".join(
                f"  [{tid}]: {result[:500]}" for tid, result in dep_results.items()
            )

        prompt = f"""You are an AI agent executing a specific sub-task within the Kovrin orchestration framework.

TASK: {subtask.description}

CONTEXT: {intent_context or "Not provided"}
{dep_context}

Execute this task thoroughly and provide a clear, structured result.
Focus on quality and accuracy. If the task requires analysis, be specific.
If it requires generation, be creative yet precise."""

        # OTEL tracing
        from kovrin.observability.metrics import measure_task_duration, record_task_complete, record_tool_call
        from kovrin.observability.tracing import get_tracer

        tracer = get_tracer()

        # Execute via Claude API
        subtask.status = TaskStatus.EXECUTING
        traces.append(
            Trace(
                intent_id=subtask.parent_intent_id or "",
                task_id=subtask.id,
                event_type="EXECUTION_START",
                description=f"Executing: {subtask.description[:60]}",
                risk_level=subtask.risk_level,
            )
        )

        # Build API call kwargs
        messages = [{"role": "user", "content": prompt}]
        api_kwargs: dict = {
            "model": self._model,
            "max_tokens": 4096,
            "messages": messages,
        }

        # Add tools if registry is available
        if self._tool_registry:
            tool_schemas = self._tool_registry.get_schemas_for_task(subtask)
            if tool_schemas:
                api_kwargs["tools"] = tool_schemas

        with tracer.start_as_current_span("kovrin.task_execute") as task_span:
            task_span.set_attribute("kovrin.task_id", subtask.id)
            task_span.set_attribute("kovrin.risk_level", subtask.risk_level.value)
            task_span.set_attribute("kovrin.model", self._model)

            with measure_task_duration(subtask.id, subtask.risk_level.value):
                response = await self._client.messages.create(**api_kwargs)

                # Tool use loop: handle tool_use responses with safety-gated execution
                rounds = 0
                while (
                    response.stop_reason == "tool_use"
                    and self._tool_router
                    and self._tool_registry
                    and rounds < MAX_TOOL_ROUNDS
                ):
                    rounds += 1

                    tool_results = []
                    for block in response.content:
                        if block.type == "tool_use":
                            from kovrin.tools.models import ToolCallRequest

                            request = ToolCallRequest(
                                tool_name=block.name,
                                tool_input=block.input,
                                tool_use_id=block.id,
                                task_id=subtask.id,
                                intent_id=subtask.parent_intent_id or "",
                            )

                            # Route through safety pipeline
                            with tracer.start_as_current_span("kovrin.tool_call") as tool_span:
                                tool_span.set_attribute("kovrin.tool_name", block.name)
                                decision = await self._tool_router.evaluate(request)
                                tool_span.set_attribute("kovrin.tool_allowed", decision.allowed)
                                tool_span.set_attribute("kovrin.tool_risk", decision.risk_level.value)

                                if decision.allowed:
                                    tool_result = await self._tool_router.execute_if_allowed(
                                        request, decision
                                    )
                                else:
                                    from kovrin.agents.tools import ToolResult

                                    tool_result = ToolResult(
                                        tool_use_id=block.id,
                                        content=f"[BLOCKED BY SAFETY] {decision.reason}",
                                        is_error=True,
                                    )

                            record_tool_call(
                                tool_name=block.name,
                                allowed=decision.allowed,
                                risk_level=decision.risk_level.value,
                            )

                            tool_results.append(tool_result)

                            traces.append(
                                Trace(
                                    intent_id=subtask.parent_intent_id or "",
                                    task_id=subtask.id,
                                    event_type="TOOL_CALL",
                                    description=f"Tool '{block.name}' → {decision.action.value}",
                                    details={
                                        "tool": block.name,
                                        "allowed": decision.allowed,
                                        "action": decision.action.value,
                                        "risk_level": decision.risk_level.value,
                                        "result_preview": tool_result.content[:200],
                                        "is_error": tool_result.is_error,
                                    },
                                    risk_level=decision.risk_level,
                                )
                            )

                    # Add assistant response + tool results to messages
                    messages.append({"role": "assistant", "content": response.content})
                    messages.append(
                        {
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
                        }
                    )

                    api_kwargs["messages"] = messages
                    response = await self._client.messages.create(**api_kwargs)

            task_span.set_attribute("kovrin.tool_rounds", rounds)

        # Extract final text result
        result = ""
        for block in response.content:
            if hasattr(block, "text"):
                result += block.text

        subtask.status = TaskStatus.COMPLETED
        subtask.output = result

        record_task_complete(
            task_id=subtask.id,
            success=True,
            risk_level=subtask.risk_level.value,
        )

        traces.append(
            Trace(
                intent_id=subtask.parent_intent_id or "",
                task_id=subtask.id,
                event_type="EXECUTION_COMPLETE",
                description=f"Completed: {subtask.description[:60]}",
                details={"output_length": len(result), "tool_rounds": rounds, "model": self._model},
                risk_level=subtask.risk_level,
            )
        )

        # Optional PRM evaluation
        if self._prm:
            from kovrin.engine.prm import ProcessRewardModel

            prm_score = await self._prm.evaluate(subtask, result, intent_context)
            traces.append(
                ProcessRewardModel.create_trace(subtask, prm_score, subtask.parent_intent_id or "")
            )
            if self._prm.is_below_threshold(prm_score):
                traces.append(
                    Trace(
                        intent_id=subtask.parent_intent_id or "",
                        task_id=subtask.id,
                        event_type="PRM_LOW_QUALITY",
                        description=f"PRM below threshold ({prm_score.aggregate_score:.2f} < {self._prm.threshold}): {subtask.description[:50]}",
                        details={
                            "aggregate_score": prm_score.aggregate_score,
                            "threshold": self._prm.threshold,
                        },
                        risk_level=subtask.risk_level,
                    )
                )

        return result, traces

    async def execute_for_graph(
        self,
        subtask: SubTask,
        dep_results: dict[str, str],
    ) -> str:
        """Simplified execute interface for GraphExecutor compatibility.

        GraphExecutor expects: async (SubTask, dict[str, str]) -> str
        This adapter strips the traces (they're logged separately).
        """
        result, _ = await self.execute(subtask, dep_results)
        return result
