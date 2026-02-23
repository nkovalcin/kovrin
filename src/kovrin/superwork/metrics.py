"""
Metrics Tracker — Velocity, Cost, and Completion Prediction

Pure Python module with no external dependencies. Tracks task
completions, token usage, and produces real-time metrics snapshots
and completion predictions.
"""

from __future__ import annotations

from datetime import UTC, datetime, timedelta

from kovrin.superwork.models import (
    MetricsSnapshot,
    PredictionResult,
    TaskCompletionEvent,
)

# Approximate Claude Sonnet pricing (USD per token)
COST_PER_INPUT_TOKEN = 3.0 / 1_000_000
COST_PER_OUTPUT_TOKEN = 15.0 / 1_000_000

# Default estimate when exact token count is unavailable
DEFAULT_TOKENS_PER_TASK = 2000


class MetricsTracker:
    """Tracks SuperWork session metrics and produces predictions.

    Fed by TaskCompletionEvent from the Session Watcher.
    Snapshots can be persisted via SuperWorkRepository.
    """

    def __init__(self) -> None:
        self._completed: list[TaskCompletionEvent] = []
        self._failed: list[TaskCompletionEvent] = []
        self._total_input_tokens: int = 0
        self._total_output_tokens: int = 0
        self._estimated_tokens: int = 0
        self._session_start: datetime = datetime.now(UTC)

    def record_completion(self, event: TaskCompletionEvent) -> None:
        """Record a task completion event.

        Events with errors are counted as failures.
        Token usage is estimated when exact counts are unavailable.

        Args:
            event: Task completion event from Session Watcher.
        """
        if event.errors:
            self._failed.append(event)
        else:
            self._completed.append(event)
        self._estimated_tokens += DEFAULT_TOKENS_PER_TASK

    def record_tokens(self, input_tokens: int, output_tokens: int) -> None:
        """Record exact token usage when available from API responses.

        Args:
            input_tokens: Number of input tokens consumed.
            output_tokens: Number of output tokens generated.
        """
        self._total_input_tokens += input_tokens
        self._total_output_tokens += output_tokens

    @property
    def tasks_completed(self) -> int:
        """Number of successfully completed tasks."""
        return len(self._completed)

    @property
    def tasks_failed(self) -> int:
        """Number of failed tasks."""
        return len(self._failed)

    @property
    def total_tasks(self) -> int:
        """Total tasks processed (completed + failed)."""
        return self.tasks_completed + self.tasks_failed

    @property
    def velocity(self) -> float:
        """Tasks completed per hour based on session duration."""
        hours = self.session_duration_hours
        if hours < 0.01:
            return 0.0
        return self.tasks_completed / hours

    @property
    def success_rate(self) -> float:
        """Ratio of successful tasks to total tasks."""
        if self.total_tasks == 0:
            return 1.0
        return self.tasks_completed / self.total_tasks

    @property
    def total_tokens(self) -> int:
        """Total tokens used (exact + estimated)."""
        return self._total_input_tokens + self._total_output_tokens + self._estimated_tokens

    @property
    def cost_usd(self) -> float:
        """Estimated cost in USD."""
        exact_cost = (
            self._total_input_tokens * COST_PER_INPUT_TOKEN
            + self._total_output_tokens * COST_PER_OUTPUT_TOKEN
        )
        estimated_cost = self._estimated_tokens * COST_PER_OUTPUT_TOKEN
        return exact_cost + estimated_cost

    @property
    def session_duration_hours(self) -> float:
        """Session duration in hours."""
        elapsed = (datetime.now(UTC) - self._session_start).total_seconds()
        return elapsed / 3600

    def snapshot(self) -> MetricsSnapshot:
        """Create a point-in-time metrics snapshot.

        Returns:
            MetricsSnapshot with current values.
        """
        return MetricsSnapshot(
            tasks_completed=self.tasks_completed,
            tasks_failed=self.tasks_failed,
            tokens_used=self.total_tokens,
            cost_usd=round(self.cost_usd, 4),
            velocity_tasks_per_hour=round(self.velocity, 2),
            success_rate=round(self.success_rate, 4),
            session_duration_seconds=int((datetime.now(UTC) - self._session_start).total_seconds()),
        )

    def predict(self, remaining_tasks: int) -> PredictionResult:
        """Predict completion time and cost for remaining tasks.

        Uses current velocity and cost-per-task to extrapolate.
        Confidence increases with more completed tasks.

        Args:
            remaining_tasks: Estimated number of tasks remaining.

        Returns:
            PredictionResult with ETA, cost, and confidence.
        """
        if self.velocity < 0.01 or self.tasks_completed == 0:
            return PredictionResult(
                remaining_tasks=remaining_tasks,
                confidence=0.1,
            )

        hours = remaining_tasks / self.velocity
        cost_per_task = self.cost_usd / self.tasks_completed
        cost = remaining_tasks * cost_per_task

        return PredictionResult(
            remaining_tasks=remaining_tasks,
            estimated_hours=round(hours, 1),
            estimated_cost_usd=round(cost, 2),
            estimated_completion=datetime.now(UTC) + timedelta(hours=hours),
            confidence=min(0.9, 0.3 + (self.tasks_completed * 0.05)),
        )
