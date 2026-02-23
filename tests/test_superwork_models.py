"""Tests for SuperWork data models."""

from datetime import datetime

import pytest
from pydantic import ValidationError

from kovrin.core.models import RiskLevel
from kovrin.superwork.models import (
    MetricsSnapshot,
    PredictionResult,
    ProjectAnalysis,
    ProposalStatus,
    SessionStatus,
    SuperWorkSession,
    TaskCompletionEvent,
    TaskProposal,
)

# ── Enum Tests ───────────────────────────────────────────────────


class TestSessionStatus:
    def test_all_values(self):
        assert set(SessionStatus) == {
            SessionStatus.INITIALIZING,
            SessionStatus.WATCHING,
            SessionStatus.PAUSED,
            SessionStatus.STOPPED,
        }

    def test_string_values(self):
        assert SessionStatus.INITIALIZING.value == "INITIALIZING"
        assert SessionStatus.WATCHING.value == "WATCHING"
        assert SessionStatus.PAUSED.value == "PAUSED"
        assert SessionStatus.STOPPED.value == "STOPPED"

    def test_is_str_enum(self):
        assert isinstance(SessionStatus.WATCHING, str)


class TestProposalStatus:
    def test_all_values(self):
        assert set(ProposalStatus) == {
            ProposalStatus.PENDING,
            ProposalStatus.APPROVED,
            ProposalStatus.SKIPPED,
            ProposalStatus.EXECUTING,
            ProposalStatus.COMPLETED,
            ProposalStatus.FAILED,
        }

    def test_string_values(self):
        assert ProposalStatus.PENDING.value == "PENDING"
        assert ProposalStatus.APPROVED.value == "APPROVED"


# ── TaskCompletionEvent Tests ────────────────────────────────────


class TestTaskCompletionEvent:
    def test_defaults(self):
        event = TaskCompletionEvent()
        assert event.id.startswith("tce-")
        assert event.session_id == ""
        assert event.completed_task == ""
        assert event.files_changed == []
        assert event.errors == []
        assert event.duration_seconds == 0
        assert isinstance(event.timestamp, datetime)

    def test_with_data(self):
        event = TaskCompletionEvent(
            completed_task="Fix login bug",
            files_changed=["src/auth.py"],
            errors=["TypeError at line 42"],
            duration_seconds=120,
        )
        assert event.completed_task == "Fix login bug"
        assert event.files_changed == ["src/auth.py"]
        assert event.errors == ["TypeError at line 42"]
        assert event.duration_seconds == 120

    def test_unique_ids(self):
        e1 = TaskCompletionEvent()
        e2 = TaskCompletionEvent()
        assert e1.id != e2.id


# ── TaskProposal Tests ──────────────────────────────────────────


class TestTaskProposal:
    def test_required_fields(self):
        proposal = TaskProposal(title="Add tests", description="Write unit tests")
        assert proposal.title == "Add tests"
        assert proposal.description == "Write unit tests"

    def test_defaults(self):
        proposal = TaskProposal(title="T", description="D")
        assert proposal.id.startswith("prop-")
        assert proposal.rationale == ""
        assert proposal.risk_level == RiskLevel.LOW
        assert proposal.estimated_tokens == 0
        assert proposal.auto_execute is False
        assert proposal.dependencies == []
        assert proposal.status == ProposalStatus.PENDING
        assert proposal.priority == 0
        assert proposal.resolved_at is None

    def test_missing_required_raises(self):
        with pytest.raises(ValidationError):
            TaskProposal()

    def test_risk_level_assignment(self):
        proposal = TaskProposal(
            title="Delete DB",
            description="Drop all tables",
            risk_level=RiskLevel.CRITICAL,
        )
        assert proposal.risk_level == RiskLevel.CRITICAL


# ── ProjectAnalysis Tests ───────────────────────────────────────


class TestProjectAnalysis:
    def test_defaults(self):
        analysis = ProjectAnalysis()
        assert analysis.id.startswith("analysis-")
        assert analysis.total_tasks_completed == 0
        assert analysis.proposals == []
        assert analysis.status == "ok"

    def test_with_proposals(self):
        p = TaskProposal(title="T", description="D")
        analysis = ProjectAnalysis(proposals=[p])
        assert len(analysis.proposals) == 1


# ── MetricsSnapshot Tests ──────────────────────────────────────


class TestMetricsSnapshot:
    def test_defaults(self):
        snap = MetricsSnapshot()
        assert snap.tasks_completed == 0
        assert snap.tasks_failed == 0
        assert snap.tokens_used == 0
        assert snap.cost_usd == 0.0
        assert snap.velocity_tasks_per_hour == 0.0
        assert snap.success_rate == 1.0
        assert snap.session_duration_seconds == 0

    def test_custom_values(self):
        snap = MetricsSnapshot(
            tasks_completed=10,
            tasks_failed=2,
            cost_usd=1.50,
            velocity_tasks_per_hour=5.0,
        )
        assert snap.tasks_completed == 10
        assert snap.cost_usd == 1.50


# ── PredictionResult Tests ──────────────────────────────────────


class TestPredictionResult:
    def test_defaults(self):
        pred = PredictionResult()
        assert pred.remaining_tasks == 0
        assert pred.estimated_hours == 0.0
        assert pred.estimated_cost_usd == 0.0
        assert pred.estimated_completion is None
        assert pred.confidence == 0.5

    def test_confidence_bounds(self):
        pred = PredictionResult(confidence=0.0)
        assert pred.confidence == 0.0
        pred = PredictionResult(confidence=1.0)
        assert pred.confidence == 1.0

    def test_confidence_out_of_range(self):
        with pytest.raises(ValidationError):
            PredictionResult(confidence=1.5)
        with pytest.raises(ValidationError):
            PredictionResult(confidence=-0.1)


# ── SuperWorkSession Tests ──────────────────────────────────────


class TestSuperWorkSession:
    def test_required_fields(self):
        session = SuperWorkSession(project_path="/tmp/project")
        assert session.project_path == "/tmp/project"

    def test_defaults(self):
        session = SuperWorkSession(project_path="/tmp")
        assert session.id.startswith("sw-")
        assert session.status == SessionStatus.INITIALIZING
        assert isinstance(session.started_at, datetime)
        assert session.stopped_at is None
        assert isinstance(session.metrics, MetricsSnapshot)
        assert session.active_proposals == []

    def test_missing_project_path_raises(self):
        with pytest.raises(ValidationError):
            SuperWorkSession()
