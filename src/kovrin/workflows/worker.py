"""Temporal worker entry point for Kovrin.

Runs as a separate process/service that picks up pipeline workflow
executions from the Temporal task queue.

Usage:
    python -m kovrin.workflows.worker

Environment variables:
    TEMPORAL_ADDRESS: Temporal server address (default: localhost:7233)
    TEMPORAL_NAMESPACE: Temporal namespace (default: default)
    TEMPORAL_TASK_QUEUE: Task queue name (default: kovrin-pipeline)
"""

from __future__ import annotations

import asyncio
import os


async def run_worker() -> None:
    """Start the Temporal worker."""
    try:
        from temporalio.client import Client
        from temporalio.worker import Worker
    except ImportError as e:
        raise ImportError(
            "temporalio is required for Temporal workers. "
            "Install with: pip install 'kovrin[temporal]'"
        ) from e

    from kovrin.workflows.activities import _get_activity_definitions
    from kovrin.workflows.pipeline_workflow import TASK_QUEUE, _get_workflow_class

    address = os.environ.get("TEMPORAL_ADDRESS", "localhost:7233")
    namespace = os.environ.get("TEMPORAL_NAMESPACE", "default")
    task_queue = os.environ.get("TEMPORAL_TASK_QUEUE", TASK_QUEUE)

    print(f"[kovrin-worker] Connecting to Temporal at {address} (namespace={namespace})")
    client = await Client.connect(address, namespace=namespace)

    PipelineWorkflow = _get_workflow_class()
    parse_intent, evaluate_critics, execute_task = _get_activity_definitions()

    worker = Worker(
        client,
        task_queue=task_queue,
        workflows=[PipelineWorkflow],
        activities=[parse_intent, evaluate_critics, execute_task],
    )

    print(f"[kovrin-worker] Listening on task queue: {task_queue}")
    await worker.run()


def main() -> None:
    """Entry point for `python -m kovrin.workflows.worker`."""
    asyncio.run(run_worker())


if __name__ == "__main__":
    main()
