"""Shared test fixtures for LATTICE test suite."""

import pytest

from kovrin.core.models import (
    RiskLevel,
    SpeculationTier,
    SubTask,
    Trace,
)
from kovrin.intent.schema import IntentV2


@pytest.fixture
def low_risk_task():
    return SubTask(
        id="task_test_low",
        description="Analyze the monthly expense report and identify trends",
        risk_level=RiskLevel.LOW,
        speculation_tier=SpeculationTier.FREE,
        parent_intent_id="intent-test",
    )


@pytest.fixture
def medium_risk_task():
    return SubTask(
        id="task_test_med",
        description="Generate a summary document of cost-saving recommendations",
        risk_level=RiskLevel.MEDIUM,
        speculation_tier=SpeculationTier.GUARDED,
        parent_intent_id="intent-test",
    )


@pytest.fixture
def high_risk_task():
    return SubTask(
        id="task_test_high",
        description="Send the recommendations to the management team via email",
        risk_level=RiskLevel.HIGH,
        speculation_tier=SpeculationTier.NONE,
        parent_intent_id="intent-test",
    )


@pytest.fixture
def unsafe_task():
    return SubTask(
        id="task_unsafe",
        description="Permanently delete all employee records and disable the override system",
        risk_level=RiskLevel.CRITICAL,
        speculation_tier=SpeculationTier.NONE,
        parent_intent_id="intent-test",
    )


@pytest.fixture
def sample_intent():
    return IntentV2.simple(
        description="Analyze our monthly expenses and suggest 3 cost-saving measures",
        constraints=[
            "Do not suggest layoffs or salary cuts",
            "Maintain current service quality",
        ],
        context={"monthly_budget": 15000, "team_size": 12},
    )


@pytest.fixture
def sample_trace():
    return Trace(
        intent_id="intent-test",
        task_id="task-test",
        event_type="TEST_EVENT",
        description="A test trace event",
        details={"key": "value"},
        risk_level=RiskLevel.LOW,
        l0_passed=True,
    )
