"""Kovrin Workflows — Temporal-based durable execution.

Opt-in via TEMPORAL_ADDRESS env var.
Without it, the pipeline runs with asyncio.create_task (current behavior).

When enabled:
- Each pipeline run becomes a Temporal workflow
- Human approval uses Temporal signals
- Activities wrap existing pipeline stages (parse, evaluate, execute)
- Automatic retries, timeouts, and visibility via Temporal UI
"""

__all__: list[str] = []
