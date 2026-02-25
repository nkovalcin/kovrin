"""Temporal activities for Kovrin pipeline stages.

Each activity wraps an existing pipeline stage, making it a retriable,
observable unit of work within a Temporal workflow.

Activities are designed to be idempotent where possible.
"""

from __future__ import annotations

import json
from dataclasses import dataclass


@dataclass
class ParseIntentInput:
    """Input for parse_intent activity."""

    intent: str
    constraints: list[str]
    context: dict


@dataclass
class ParseIntentOutput:
    """Output from parse_intent activity."""

    intent_id: str
    subtask_ids: list[str]
    subtasks_json: str  # Serialized list of SubTask dicts


@dataclass
class EvaluateCriticsInput:
    """Input for evaluate_critics activity."""

    subtasks_json: str
    constraints: list[str]
    intent_context: str
    task_context_json: str


@dataclass
class EvaluateCriticsOutput:
    """Output from evaluate_critics activity."""

    approved_ids: list[str]
    rejected_ids: list[str]
    all_subtasks_json: str  # Updated with statuses


@dataclass
class ExecuteTaskInput:
    """Input for execute_task activity."""

    subtask_json: str
    dep_results_json: str
    intent_context: str


@dataclass
class ExecuteTaskOutput:
    """Output from execute_task activity."""

    task_id: str
    result_text: str
    success: bool
    traces_json: str


def _get_activity_definitions():
    """Return activity functions. Only importable when temporalio is installed."""
    try:
        from temporalio import activity
    except ImportError as e:
        raise ImportError(
            "temporalio is required for Temporal workflows. "
            "Install with: pip install 'kovrin[temporal]'"
        ) from e

    @activity.defn(name="parse_intent")
    async def parse_intent(input: ParseIntentInput) -> ParseIntentOutput:
        """Parse user intent into sub-tasks."""
        import anthropic

        from kovrin.intent.parser import IntentParser
        from kovrin.intent.schema import IntentV2

        client = anthropic.AsyncAnthropic()
        parser = IntentParser(client)

        intent_obj = IntentV2.simple(
            description=input.intent,
            constraints=input.constraints,
            context=input.context,
        )
        subtasks = await parser.parse(intent_obj)

        return ParseIntentOutput(
            intent_id=intent_obj.id,
            subtask_ids=[t.id for t in subtasks],
            subtasks_json=json.dumps([t.model_dump() for t in subtasks], default=str),
        )

    @activity.defn(name="evaluate_critics")
    async def evaluate_critics(input: EvaluateCriticsInput) -> EvaluateCriticsOutput:
        """Validate sub-tasks through the critic pipeline."""
        import anthropic

        from kovrin.core.constitutional import ConstitutionalCore
        from kovrin.core.models import SubTask, TaskStatus
        from kovrin.safety.critics import (
            CriticPipeline,
            FeasibilityCritic,
            PolicyCritic,
            SafetyCritic,
        )

        client = anthropic.AsyncAnthropic()
        constitutional = ConstitutionalCore(client)
        critics = CriticPipeline(
            SafetyCritic(constitutional),
            FeasibilityCritic(client),
            PolicyCritic(client),
        )

        subtasks = [SubTask(**d) for d in json.loads(input.subtasks_json)]
        context = json.loads(input.task_context_json) if input.task_context_json else None

        approved_ids = []
        rejected_ids = []

        for subtask in subtasks:
            passed, obligations = await critics.evaluate(
                subtask=subtask,
                constraints=input.constraints,
                intent_context=input.intent_context,
                task_context=context,
            )
            subtask.proof_obligations = obligations
            if passed:
                approved_ids.append(subtask.id)
            else:
                subtask.status = TaskStatus.REJECTED_BY_L0
                rejected_ids.append(subtask.id)

        return EvaluateCriticsOutput(
            approved_ids=approved_ids,
            rejected_ids=rejected_ids,
            all_subtasks_json=json.dumps([t.model_dump() for t in subtasks], default=str),
        )

    @activity.defn(name="execute_task")
    async def execute_task(input: ExecuteTaskInput) -> ExecuteTaskOutput:
        """Execute a single sub-task via Claude API."""
        import anthropic

        from kovrin.core.models import SubTask
        from kovrin.engine.executor import TaskExecutor
        from kovrin.engine.risk_router import RiskRouter

        client = anthropic.AsyncAnthropic()
        executor = TaskExecutor(client, RiskRouter())

        subtask = SubTask(**json.loads(input.subtask_json))
        dep_results = json.loads(input.dep_results_json) if input.dep_results_json else {}

        try:
            result, traces = await executor.execute(subtask, dep_results, input.intent_context)
            return ExecuteTaskOutput(
                task_id=subtask.id,
                result_text=result,
                success=True,
                traces_json=json.dumps([t.model_dump() for t in traces], default=str),
            )
        except Exception as e:
            return ExecuteTaskOutput(
                task_id=subtask.id,
                result_text=f"Error: {e}",
                success=False,
                traces_json="[]",
            )

    return parse_intent, evaluate_critics, execute_task
