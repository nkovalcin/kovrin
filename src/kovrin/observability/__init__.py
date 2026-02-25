"""Kovrin Observability — OpenTelemetry tracing and metrics.

Opt-in via OTEL_EXPORTER_OTLP_ENDPOINT env var.
Without it, all tracing/metrics calls are no-ops.
"""

from kovrin.observability.metrics import (
    record_pipeline_complete,
    record_task_complete,
    record_task_duration,
    record_tool_call,
)
from kovrin.observability.tracing import get_tracer, init_tracing

__all__ = [
    "init_tracing",
    "get_tracer",
    "record_pipeline_complete",
    "record_task_complete",
    "record_task_duration",
    "record_tool_call",
]
