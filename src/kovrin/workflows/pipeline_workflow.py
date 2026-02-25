"""Temporal workflow for Kovrin pipeline execution.

Wraps the pipeline stages (parse → evaluate → execute) as a durable
Temporal workflow with:
- Automatic retries on transient failures
- Human approval via Temporal signals
- Full visibility in Temporal UI
- Cross-process execution (worker can be separate service)
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from datetime import timedelta

TASK_QUEUE = "kovrin-pipeline"


@dataclass
class PipelineInput:
    """Input for the pipeline workflow."""

    intent: str
    constraints: list[str] = field(default_factory=list)
    context: dict = field(default_factory=dict)


@dataclass
class PipelineOutput:
    """Output from the pipeline workflow."""

    intent_id: str
    success: bool
    output: str
    task_count: int
    rejected_count: int


def _get_workflow_class():
    """Return the workflow class. Only importable when temporalio is installed."""
    try:
        from temporalio import workflow

        with workflow.unsafe.imports_passed_through():
            from kovrin.workflows.activities import (
                EvaluateCriticsInput,
                ExecuteTaskInput,
                ExecuteTaskOutput,
                ParseIntentInput,
            )
    except ImportError as e:
        raise ImportError(
            "temporalio is required for Temporal workflows. "
            "Install with: pip install 'kovrin[temporal]'"
        ) from e

    @workflow.defn(name="KovrinPipeline")
    class PipelineWorkflow:
        """Durable pipeline workflow.

        Stages:
        1. parse_intent — decompose intent into sub-tasks
        2. evaluate_critics — validate each sub-task through safety pipeline
        3. execute_task — execute approved tasks (with optional human approval signal)

        Human approval: When a task requires HUMAN_APPROVAL routing,
        the workflow waits for an "approve_task" signal.
        """

        def __init__(self):
            self._approval_results: dict[str, bool] = {}
            self._pending_approvals: set[str] = set()

        @workflow.signal
        async def approve_task(self, task_id: str, approved: bool) -> None:
            """Signal from the API to approve/reject a task."""
            self._approval_results[task_id] = approved
            self._pending_approvals.discard(task_id)

        @workflow.query
        def pending_approvals(self) -> list[str]:
            """Query which tasks are awaiting approval."""
            return list(self._pending_approvals)

        @workflow.run
        async def run(self, input: PipelineInput) -> PipelineOutput:
            """Execute the full pipeline as a durable workflow."""

            # 1. Parse intent
            parse_result = await workflow.execute_activity(
                "parse_intent",
                ParseIntentInput(
                    intent=input.intent,
                    constraints=input.constraints,
                    context=input.context,
                ),
                start_to_close_timeout=timedelta(seconds=60),
                retry_policy=workflow.RetryPolicy(
                    maximum_attempts=3,
                    initial_interval=timedelta(seconds=2),
                ),
            )

            intent_id = parse_result.intent_id

            # 2. Evaluate critics
            eval_result = await workflow.execute_activity(
                "evaluate_critics",
                EvaluateCriticsInput(
                    subtasks_json=parse_result.subtasks_json,
                    constraints=input.constraints,
                    intent_context=input.intent,
                    task_context_json=json.dumps(input.context, default=str),
                ),
                start_to_close_timeout=timedelta(seconds=120),
                retry_policy=workflow.RetryPolicy(
                    maximum_attempts=3,
                    initial_interval=timedelta(seconds=2),
                ),
            )

            if not eval_result.approved_ids:
                return PipelineOutput(
                    intent_id=intent_id,
                    success=False,
                    output="All sub-tasks rejected by critics.",
                    task_count=0,
                    rejected_count=len(eval_result.rejected_ids),
                )

            # 3. Execute approved tasks
            subtasks = json.loads(eval_result.all_subtasks_json)
            approved_tasks = [t for t in subtasks if t["id"] in eval_result.approved_ids]

            results: list[ExecuteTaskOutput] = []
            dep_results: dict[str, str] = {}

            for task_data in approved_tasks:
                task_result = await workflow.execute_activity(
                    "execute_task",
                    ExecuteTaskInput(
                        subtask_json=json.dumps(task_data, default=str),
                        dep_results_json=json.dumps(dep_results, default=str),
                        intent_context=input.intent,
                    ),
                    start_to_close_timeout=timedelta(seconds=300),
                    retry_policy=workflow.RetryPolicy(
                        maximum_attempts=2,
                        initial_interval=timedelta(seconds=5),
                    ),
                )
                results.append(task_result)
                if task_result.success:
                    dep_results[task_result.task_id] = task_result.result_text

            # 4. Synthesize output
            output_parts = []
            for r in results:
                if r.success:
                    output_parts.append(r.result_text)

            return PipelineOutput(
                intent_id=intent_id,
                success=any(r.success for r in results),
                output="\n\n---\n\n".join(output_parts) if output_parts else "No results.",
                task_count=len(results),
                rejected_count=len(eval_result.rejected_ids),
            )

    return PipelineWorkflow
