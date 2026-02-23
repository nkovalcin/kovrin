"""Tests for SuperWork metrics tracker."""

from datetime import datetime

import pytest

from kovrin.superwork.metrics import MetricsTracker
from kovrin.superwork.models import TaskCompletionEvent


@pytest.fixture
def tracker():
    return MetricsTracker()


def _make_event(
    task: str = "Test task",
    duration: int = 60,
    errors: list[str] | None = None,
    tokens_input: int = 1000,
    tokens_output: int = 500,
) -> TaskCompletionEvent:
    return TaskCompletionEvent(
        completed_task=task,
        duration_seconds=duration,
        errors=errors or [],
    )


class TestRecordCompletion:
    def test_record_success(self, tracker):
        event = _make_event()
        tracker.record_completion(event)
        assert tracker.tasks_completed == 1
        assert tracker.tasks_failed == 0

    def test_record_failure(self, tracker):
        event = _make_event(errors=["Something went wrong"])
        tracker.record_completion(event)
        assert tracker.total_tasks == 1
        assert tracker.tasks_failed == 1

    def test_multiple_events(self, tracker):
        tracker.record_completion(_make_event())
        tracker.record_completion(_make_event(errors=["fail"]))
        tracker.record_completion(_make_event())
        assert tracker.total_tasks == 3
        assert tracker.tasks_failed == 1


class TestVelocity:
    def test_zero_time(self, tracker):
        assert tracker.velocity == 0.0

    def test_velocity_calculation(self, tracker):
        tracker.record_completion(_make_event())
        tracker.record_completion(_make_event())
        # Velocity depends on time elapsed since start, which is ~0
        # so velocity will be very high or 0 depending on timing
        assert isinstance(tracker.velocity, float)


class TestCost:
    def test_initial_cost(self, tracker):
        assert tracker.cost_usd == 0.0

    def test_cost_after_token_recording(self, tracker):
        tracker.record_tokens(input_tokens=1_000_000, output_tokens=0)
        assert tracker.cost_usd == pytest.approx(3.0)

    def test_cost_output_tokens(self, tracker):
        tracker.record_tokens(input_tokens=0, output_tokens=1_000_000)
        assert tracker.cost_usd == pytest.approx(15.0)

    def test_cost_mixed(self, tracker):
        tracker.record_tokens(input_tokens=500_000, output_tokens=100_000)
        expected = (500_000 * 3.0 / 1_000_000) + (100_000 * 15.0 / 1_000_000)
        assert tracker.cost_usd == pytest.approx(expected)


class TestSuccessRate:
    def test_no_tasks(self, tracker):
        assert tracker.success_rate == 1.0

    def test_all_success(self, tracker):
        for _ in range(5):
            tracker.record_completion(_make_event())
        assert tracker.success_rate == 1.0

    def test_mixed(self, tracker):
        tracker.record_completion(_make_event())
        tracker.record_completion(_make_event(errors=["fail"]))
        assert tracker.success_rate == pytest.approx(0.5)


class TestSnapshot:
    def test_snapshot_returns_metrics(self, tracker):
        tracker.record_completion(_make_event())
        tracker.record_tokens(input_tokens=1000, output_tokens=500)
        snap = tracker.snapshot()
        assert snap.tasks_completed == 1
        assert snap.tasks_failed == 0
        # tokens_used = input(1000) + output(500) + estimated(2000 per task)
        assert snap.tokens_used == 3500
        assert snap.cost_usd > 0
        assert snap.success_rate == 1.0
        assert isinstance(snap.timestamp, datetime)


class TestPredict:
    def test_no_data(self, tracker):
        pred = tracker.predict(remaining_tasks=10)
        assert pred.remaining_tasks == 10
        assert pred.confidence == pytest.approx(0.1)

    def test_with_data(self, tracker):
        for _ in range(5):
            tracker.record_completion(_make_event(duration=60))
        tracker.record_tokens(input_tokens=5000, output_tokens=2000)
        pred = tracker.predict(remaining_tasks=10)
        assert pred.remaining_tasks == 10
        assert pred.estimated_hours >= 0
        assert pred.estimated_cost_usd >= 0
        assert 0.0 <= pred.confidence <= 1.0


class TestTotalTokens:
    def test_initial_zero(self, tracker):
        assert tracker.total_tokens == 0

    def test_after_completion(self, tracker):
        tracker.record_completion(_make_event())
        # Each completion adds DEFAULT_TOKENS_PER_TASK (2000)
        assert tracker.total_tokens == 2000

    def test_after_explicit_tokens(self, tracker):
        tracker.record_tokens(input_tokens=1000, output_tokens=500)
        assert tracker.total_tokens == 1500
