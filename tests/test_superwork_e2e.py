"""End-to-end SuperWork pipeline test.

Wires all SuperWork components together with mocked external dependencies
(watchdog, chromadb, anthropic) and verifies the full flow:
  SessionWatcher event → MetricsTracker → Orchestrator → Repository → retrieve
"""

import json
from unittest.mock import AsyncMock, MagicMock

import pytest

from kovrin.superwork.metrics import MetricsTracker
from kovrin.superwork.models import (
    ProposalStatus,
    SessionStatus,
    SuperWorkSession,
    TaskCompletionEvent,
    TaskProposal,
)
from kovrin.superwork.orchestrator import OrchestratorAgent
from kovrin.superwork.repository import SuperWorkRepository


def _make_event(task: str = "Fixed bug", errors: list[str] | None = None) -> TaskCompletionEvent:
    return TaskCompletionEvent(
        session_id="test-session",
        project_path="/tmp/project",
        completed_task=task,
        output_summary=f"Completed: {task}",
        files_changed=["src/app.py"],
        errors=errors or [],
    )


def _make_mock_client(response_json: dict) -> MagicMock:
    """Create a mock Anthropic client that returns a JSON response."""
    mock_message = MagicMock()
    mock_message.content = [MagicMock(text=json.dumps(response_json))]
    client = MagicMock()
    client.messages.create = AsyncMock(return_value=mock_message)
    return client


GOOD_ANALYSIS = {
    "summary": "Project progressing well",
    "focus_area": "Testing",
    "proposals": [
        {
            "title": "Add unit tests",
            "description": "Write tests for auth module",
            "rationale": "Improve coverage",
            "risk_level": "LOW",
            "estimated_tokens": 2000,
            "auto_execute": True,
            "priority": 0,
        },
        {
            "title": "Deploy to staging",
            "description": "Push to staging environment",
            "rationale": "Verify before prod",
            "risk_level": "HIGH",
            "estimated_tokens": 500,
            "auto_execute": True,  # Should be forced to False
            "priority": 1,
        },
        {
            "title": "Update docs",
            "description": "Refresh API documentation",
            "rationale": "Keep docs current",
            "risk_level": "LOW",
            "estimated_tokens": 1000,
            "auto_execute": False,
            "priority": 2,
        },
    ],
}


class TestFullPipelineFlow:
    """Test the complete SuperWork pipeline from event to proposal retrieval."""

    @pytest.mark.asyncio
    async def test_event_to_proposals(self):
        """Event → MetricsTracker → Orchestrator → Repository → retrieve."""
        # Setup components
        metrics = MetricsTracker()
        client = _make_mock_client(GOOD_ANALYSIS)
        orchestrator = OrchestratorAgent(
            client=client,
            metrics_tracker=metrics,
        )
        repo = SuperWorkRepository(":memory:")

        # 1. Create session
        session = SuperWorkSession(project_path="/tmp/project")
        repo.save_session(session)

        # 2. Simulate completion event
        event = _make_event("Implemented login flow")
        metrics.record_completion(event)
        orchestrator.record_completion(event)

        # 3. Orchestrator analyzes and proposes
        analysis = await orchestrator.analyze_and_propose()

        assert analysis.status == "ok"
        assert len(analysis.proposals) == 3

        # 4. Save proposals to repository
        for prop in analysis.proposals:
            repo.save_proposal(prop, session.id)

        # 5. Retrieve and verify
        saved = repo.get_proposals(session.id)
        assert len(saved) == 3
        assert saved[0].title == "Add unit tests"

        # 6. Verify metrics tracked
        snap = metrics.snapshot()
        assert snap.tasks_completed == 1

    @pytest.mark.asyncio
    async def test_multiple_events_accumulate(self):
        """Multiple events produce correct metrics and history."""
        metrics = MetricsTracker()
        orchestrator = OrchestratorAgent(
            client=_make_mock_client(GOOD_ANALYSIS),
            metrics_tracker=metrics,
        )

        # Simulate 5 task completions
        for i in range(5):
            event = _make_event(f"Task {i}")
            metrics.record_completion(event)
            orchestrator.record_completion(event)

        snap = metrics.snapshot()
        assert snap.tasks_completed == 5
        assert len(orchestrator._task_history) == 5

        # Orchestrator uses accumulated history
        analysis = await orchestrator.analyze_and_propose()
        assert analysis.status == "ok"


class TestSafetyInvariants:
    """HIGH/CRITICAL proposals must never have auto_execute=True."""

    @pytest.mark.asyncio
    async def test_high_risk_forced_no_auto_execute(self):
        orchestrator = OrchestratorAgent(
            client=_make_mock_client(GOOD_ANALYSIS),
            metrics_tracker=MetricsTracker(),
        )
        analysis = await orchestrator.analyze_and_propose()

        for prop in analysis.proposals:
            if prop.risk_level.value in ("HIGH", "CRITICAL"):
                assert prop.auto_execute is False, (
                    f"Proposal '{prop.title}' with risk={prop.risk_level} "
                    f"must not have auto_execute=True"
                )

    @pytest.mark.asyncio
    async def test_critical_risk_forced_no_auto_execute(self):
        critical_analysis = {
            "summary": "Dangerous",
            "focus_area": "Infra",
            "proposals": [
                {
                    "title": "Drop database",
                    "description": "Delete production DB",
                    "risk_level": "CRITICAL",
                    "auto_execute": True,
                    "priority": 0,
                },
            ],
        }
        orchestrator = OrchestratorAgent(
            client=_make_mock_client(critical_analysis),
            metrics_tracker=MetricsTracker(),
        )
        analysis = await orchestrator.analyze_and_propose()
        assert analysis.proposals[0].auto_execute is False


class TestErrorResilience:
    """API failures should not crash the pipeline."""

    @pytest.mark.asyncio
    async def test_api_error_returns_unavailable(self):
        client = MagicMock()
        client.messages.create = AsyncMock(side_effect=ConnectionError("timeout"))

        orchestrator = OrchestratorAgent(
            client=client,
            metrics_tracker=MetricsTracker(),
        )

        # Record an event first
        orchestrator.record_completion(_make_event("task"))

        # Analysis should gracefully fail
        analysis = await orchestrator.analyze_and_propose()
        assert analysis.status == "api_unavailable"
        assert "error" in analysis.summary.lower() or "unavailable" in analysis.summary.lower()

    @pytest.mark.asyncio
    async def test_malformed_api_response(self):
        mock_message = MagicMock()
        mock_message.content = [MagicMock(text="This is not JSON at all")]
        client = MagicMock()
        client.messages.create = AsyncMock(return_value=mock_message)

        orchestrator = OrchestratorAgent(
            client=client,
            metrics_tracker=MetricsTracker(),
        )
        analysis = await orchestrator.analyze_and_propose()
        assert analysis.status == "parse_error"


class TestRepositoryRoundTrip:
    """Session + proposals + events + metrics all persist and load correctly."""

    def test_full_round_trip(self):
        repo = SuperWorkRepository(":memory:")

        # Session
        session = SuperWorkSession(project_path="/tmp/proj")
        repo.save_session(session)
        loaded = repo.get_session(session.id)
        assert loaded is not None
        assert loaded.project_path == "/tmp/proj"

        # Proposals
        prop = TaskProposal(
            title="Test task",
            description="Do something",
            risk_level="LOW",
            dependencies=["dep-1", "dep-2"],
        )
        repo.save_proposal(prop, session.id)
        proposals = repo.get_proposals(session.id)
        assert len(proposals) == 1
        assert proposals[0].title == "Test task"

        # Update proposal status
        repo.update_proposal_status(prop.id, ProposalStatus.APPROVED)
        updated = repo.get_proposals(session.id, status=ProposalStatus.APPROVED)
        assert len(updated) == 1

        # Events
        event = _make_event("Built feature")
        repo.save_event(session.id, event)
        events = repo.get_events(session.id)
        assert len(events) == 1
        assert events[0].completed_task == "Built feature"

        # Metrics
        metrics = MetricsTracker()
        metrics.record_completion(event)
        snap = metrics.snapshot()
        repo.save_metrics(session.id, snap)
        latest = repo.get_latest_metrics(session.id)
        assert latest is not None
        assert latest.tasks_completed == 1

        # Session status update
        repo.update_session_status(session.id, SessionStatus.WATCHING)
        sessions = repo.list_sessions()
        assert len(sessions) == 1
        assert sessions[0].status == SessionStatus.WATCHING
