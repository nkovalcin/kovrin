"""OpenTelemetry metrics for Kovrin.

Counters and histograms for pipeline, task, and tool call observability.
All functions are no-ops if opentelemetry is not installed or not configured.
"""

from __future__ import annotations

import time
from contextlib import contextmanager
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Generator

_meter = None
_pipelines_total = None
_tasks_total = None
_task_duration = None
_tool_calls_total = None
_initialized = False


def _ensure_meter() -> bool:
    """Lazily initialize the meter and instruments."""
    global _meter, _pipelines_total, _tasks_total, _task_duration, _tool_calls_total, _initialized

    if _initialized:
        return _meter is not None

    _initialized = True

    try:
        from opentelemetry import metrics

        _meter = metrics.get_meter("kovrin", "2.0.0a1")

        _pipelines_total = _meter.create_counter(
            "kovrin.pipelines.total",
            description="Total pipeline executions",
            unit="1",
        )
        _tasks_total = _meter.create_counter(
            "kovrin.tasks.total",
            description="Total task executions",
            unit="1",
        )
        _task_duration = _meter.create_histogram(
            "kovrin.task.duration_seconds",
            description="Task execution duration in seconds",
            unit="s",
        )
        _tool_calls_total = _meter.create_counter(
            "kovrin.tool_calls.total",
            description="Total tool call executions",
            unit="1",
        )
        return True
    except ImportError:
        return False


def record_pipeline_complete(*, intent_id: str, success: bool, task_count: int) -> None:
    """Record a completed pipeline execution."""
    if not _ensure_meter() or _pipelines_total is None:
        return
    _pipelines_total.add(
        1,
        {"kovrin.intent_id": intent_id, "kovrin.success": str(success), "kovrin.task_count": str(task_count)},
    )


def record_task_complete(*, task_id: str, success: bool, risk_level: str = "UNKNOWN") -> None:
    """Record a completed task execution."""
    if not _ensure_meter() or _tasks_total is None:
        return
    _tasks_total.add(
        1,
        {"kovrin.task_id": task_id, "kovrin.success": str(success), "kovrin.risk_level": risk_level},
    )


def record_task_duration(*, task_id: str, duration_seconds: float, risk_level: str = "UNKNOWN") -> None:
    """Record task execution duration."""
    if not _ensure_meter() or _task_duration is None:
        return
    _task_duration.record(
        duration_seconds,
        {"kovrin.task_id": task_id, "kovrin.risk_level": risk_level},
    )


def record_tool_call(*, tool_name: str, allowed: bool, risk_level: str = "UNKNOWN") -> None:
    """Record a tool call execution."""
    if not _ensure_meter() or _tool_calls_total is None:
        return
    _tool_calls_total.add(
        1,
        {"kovrin.tool_name": tool_name, "kovrin.allowed": str(allowed), "kovrin.risk_level": risk_level},
    )


@contextmanager
def measure_task_duration(task_id: str, risk_level: str = "UNKNOWN") -> Generator[None, None, None]:
    """Context manager to measure and record task execution duration."""
    start = time.monotonic()
    try:
        yield
    finally:
        duration = time.monotonic() - start
        record_task_duration(task_id=task_id, duration_seconds=duration, risk_level=risk_level)
