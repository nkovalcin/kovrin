"""Tests for SuperWork SQLite repository."""

import pytest

from kovrin.core.models import RiskLevel
from kovrin.superwork.models import (
    MetricsSnapshot,
    ProposalStatus,
    SessionStatus,
    SuperWorkSession,
    TaskCompletionEvent,
    TaskProposal,
)
from kovrin.superwork.repository import SuperWorkRepository


@pytest.fixture
def repo():
    """In-memory SQLite repository."""
    r = SuperWorkRepository(":memory:")
    yield r
    r.close()


@pytest.fixture
def session():
    return SuperWorkSession(project_path="/tmp/test-project", status=SessionStatus.WATCHING)


# ── Session Tests ────────────────────────────────────────────────


class TestSessions:
    def test_save_and_get(self, repo, session):
        repo.save_session(session)
        retrieved = repo.get_session(session.id)
        assert retrieved is not None
        assert retrieved.id == session.id
        assert retrieved.project_path == "/tmp/test-project"
        assert retrieved.status == SessionStatus.WATCHING

    def test_get_nonexistent(self, repo):
        assert repo.get_session("nonexistent") is None

    def test_list_sessions(self, repo):
        s1 = SuperWorkSession(project_path="/a")
        s2 = SuperWorkSession(project_path="/b")
        repo.save_session(s1)
        repo.save_session(s2)
        sessions = repo.list_sessions()
        assert len(sessions) == 2

    def test_update_status(self, repo, session):
        repo.save_session(session)
        repo.update_session_status(session.id, SessionStatus.STOPPED)
        updated = repo.get_session(session.id)
        assert updated is not None
        assert updated.status == SessionStatus.STOPPED
        assert updated.stopped_at is not None

    def test_upsert_session(self, repo, session):
        repo.save_session(session)
        session_copy = session.model_copy(update={"status": SessionStatus.PAUSED})
        repo.save_session(session_copy)
        retrieved = repo.get_session(session.id)
        assert retrieved is not None
        assert retrieved.status == SessionStatus.PAUSED


# ── Proposal Tests ───────────────────────────────────────────────


class TestProposals:
    def test_save_and_get(self, repo, session):
        repo.save_session(session)
        proposal = TaskProposal(
            title="Add feature",
            description="Add user auth",
            risk_level=RiskLevel.MEDIUM,
        )
        repo.save_proposal(proposal, session.id)
        proposals = repo.get_proposals(session.id)
        assert len(proposals) == 1
        assert proposals[0].title == "Add feature"
        assert proposals[0].risk_level == RiskLevel.MEDIUM

    def test_filter_by_status(self, repo, session):
        repo.save_session(session)
        p1 = TaskProposal(title="A", description="D", status=ProposalStatus.PENDING)
        p2 = TaskProposal(title="B", description="D", status=ProposalStatus.APPROVED)
        repo.save_proposal(p1, session.id)
        repo.save_proposal(p2, session.id)
        pending = repo.get_proposals(session.id, status=ProposalStatus.PENDING)
        assert len(pending) == 1
        assert pending[0].title == "A"

    def test_update_proposal_status(self, repo, session):
        repo.save_session(session)
        proposal = TaskProposal(title="T", description="D")
        repo.save_proposal(proposal, session.id)
        repo.update_proposal_status(proposal.id, ProposalStatus.APPROVED)
        proposals = repo.get_proposals(session.id)
        assert proposals[0].status == ProposalStatus.APPROVED

    def test_dependencies_serialization(self, repo, session):
        repo.save_session(session)
        proposal = TaskProposal(
            title="T",
            description="D",
            dependencies=["dep-1", "dep-2"],
        )
        repo.save_proposal(proposal, session.id)
        retrieved = repo.get_proposals(session.id)
        assert retrieved[0].dependencies == ["dep-1", "dep-2"]


# ── Metrics Tests ────────────────────────────────────────────────


class TestMetrics:
    def test_save_and_get_latest(self, repo, session):
        repo.save_session(session)
        snap = MetricsSnapshot(
            tasks_completed=5,
            tasks_failed=1,
            cost_usd=0.50,
            velocity_tasks_per_hour=3.0,
        )
        repo.save_metrics(session.id, snap)
        latest = repo.get_latest_metrics(session.id)
        assert latest is not None
        assert latest.tasks_completed == 5
        assert latest.cost_usd == 0.50

    def test_metrics_history(self, repo, session):
        repo.save_session(session)
        for i in range(3):
            snap = MetricsSnapshot(tasks_completed=i)
            repo.save_metrics(session.id, snap)
        history = repo.get_metrics_history(session.id)
        assert len(history) == 3

    def test_no_metrics(self, repo, session):
        repo.save_session(session)
        assert repo.get_latest_metrics(session.id) is None


# ── Event Tests ──────────────────────────────────────────────────


class TestEvents:
    def test_save_and_get(self, repo, session):
        repo.save_session(session)
        event = TaskCompletionEvent(
            completed_task="Fix bug",
            files_changed=["a.py", "b.py"],
            errors=["Error 1"],
            duration_seconds=60,
        )
        repo.save_event(session.id, event)
        events = repo.get_events(session.id)
        assert len(events) == 1
        assert events[0].completed_task == "Fix bug"
        assert events[0].files_changed == ["a.py", "b.py"]
        assert events[0].errors == ["Error 1"]

    def test_event_ordering(self, repo, session):
        repo.save_session(session)
        for i in range(5):
            event = TaskCompletionEvent(completed_task=f"Task {i}")
            repo.save_event(session.id, event)
        events = repo.get_events(session.id, limit=3)
        assert len(events) == 3
