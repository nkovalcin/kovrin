"""
Kovrin Task Executor

Executes individual sub-tasks via Claude API. Each execution
generates immutable trace events for the audit log.

The executor integrates with the risk router to handle
different routing decisions:
- AUTO_EXECUTE: execute immediately
- SANDBOX_REVIEW: execute with enhanced logging (MVP)
- HUMAN_APPROVAL: request approval before execution
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Callable

import anthropic

from kovrin.core.models import (
    ApprovalRequest,
    AutonomySettings,
    RoutingAction,
    RiskLevel,
    SubTask,
    TaskStatus,
    Trace,
)
from kovrin.engine.risk_router import RiskRouter

if TYPE_CHECKING:
    from kovrin.engine.prm import ProcessRewardModel


class TaskExecutor:
    """Executes sub-tasks via Claude API with risk-aware routing."""

    MODEL = "claude-sonnet-4-20250514"

    def __init__(
        self,
        client: anthropic.AsyncAnthropic | None = None,
        risk_router: RiskRouter | None = None,
        approval_callback: Callable[[ApprovalRequest], "asyncio.Future[bool]"] | None = None,
        autonomy_settings: AutonomySettings | None = None,
        prm: ProcessRewardModel | None = None,
    ):
        self._client = client or anthropic.AsyncAnthropic()
        self._router = risk_router or RiskRouter()
        self._approval_callback = approval_callback
        self._autonomy_settings = autonomy_settings
        self._prm = prm

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
                traces.append(Trace(
                    intent_id=subtask.parent_intent_id or "",
                    task_id=subtask.id,
                    event_type="HUMAN_REJECTED",
                    description=f"Human rejected: {subtask.description[:60]}",
                    risk_level=subtask.risk_level,
                ))
                raise RuntimeError(f"Human rejected task: {subtask.description[:80]}")

            traces.append(Trace(
                intent_id=subtask.parent_intent_id or "",
                task_id=subtask.id,
                event_type="HUMAN_APPROVED",
                description=f"Human approved: {subtask.description[:60]}",
                risk_level=subtask.risk_level,
            ))

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

        # Execute via Claude API
        subtask.status = TaskStatus.EXECUTING
        traces.append(Trace(
            intent_id=subtask.parent_intent_id or "",
            task_id=subtask.id,
            event_type="EXECUTION_START",
            description=f"Executing: {subtask.description[:60]}",
            risk_level=subtask.risk_level,
        ))

        response = await self._client.messages.create(
            model=self.MODEL,
            max_tokens=4096,
            messages=[{"role": "user", "content": prompt}],
        )

        result = response.content[0].text
        subtask.status = TaskStatus.COMPLETED
        subtask.output = result

        traces.append(Trace(
            intent_id=subtask.parent_intent_id or "",
            task_id=subtask.id,
            event_type="EXECUTION_COMPLETE",
            description=f"Completed: {subtask.description[:60]}",
            details={"output_length": len(result)},
            risk_level=subtask.risk_level,
        ))

        # Optional PRM evaluation
        if self._prm:
            from kovrin.engine.prm import ProcessRewardModel
            prm_score = await self._prm.evaluate(subtask, result, intent_context)
            traces.append(ProcessRewardModel.create_trace(
                subtask, prm_score, subtask.parent_intent_id or ""
            ))
            if self._prm.is_below_threshold(prm_score):
                traces.append(Trace(
                    intent_id=subtask.parent_intent_id or "",
                    task_id=subtask.id,
                    event_type="PRM_LOW_QUALITY",
                    description=f"PRM below threshold ({prm_score.aggregate_score:.2f} < {self._prm.threshold}): {subtask.description[:50]}",
                    details={"aggregate_score": prm_score.aggregate_score, "threshold": self._prm.threshold},
                    risk_level=subtask.risk_level,
                ))

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
