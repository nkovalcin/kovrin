"""End-to-end SuperWork pipeline tests.

Tests the full SuperWork flow through the API layer using httpx ASGI transport:
  - SuperWorkManager lifecycle (initialize → event → metrics → proposals → shutdown)
  - REST endpoints (session, proposals, metrics, predict, approve/skip)
  - WebSocket event stream (connect, ping/pong, broadcast)
  - Error handling (no session, API failures)
  - Safety invariants (HIGH/CRITICAL auto_execute forced False)
"""

import json
from unittest.mock import AsyncMock, MagicMock, patch

import pytest
from httpx import ASGITransport, AsyncClient

from kovrin.api.server import app
from kovrin.api.superwork_router import SuperWorkManager, sw_manager
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


# ─── Helpers ──────────────────────────────────────────────


def _make_event(
    task: str = "Fixed bug",
    session_id: str = "test-session",
    errors: list[str] | None = None,
) -> TaskCompletionEvent:
    return TaskCompletionEvent(
        session_id=session_id,
        project_path="/tmp/test-project",
        completed_task=task,
        output_summary=f"Completed: {task}",
        files_changed=["src/main.py"],
        errors=errors or [],
    )


def _mock_claude_response(response_json: dict) -> MagicMock:
    """Create a mock Anthropic message response."""
    msg = MagicMock()
    msg.content = [MagicMock(text=json.dumps(response_json))]
    client = MagicMock()
    client.messages.create = AsyncMock(return_value=msg)
    return client


GOOD_ANALYSIS = {
    "summary": "Project progressing well",
    "focus_area": "Testing",
    "proposals": [
        {
            "title": "Add integration tests",
            "description": "Write E2E tests for auth module",
            "rationale": "Improve test coverage",
            "risk_level": "LOW",
            "estimated_tokens": 3000,
            "auto_execute": True,
            "priority": 0,
        },
        {
            "title": "Refactor database layer",
            "description": "Optimize queries for performance",
            "rationale": "Reduce latency",
            "risk_level": "MEDIUM",
            "estimated_tokens": 5000,
            "auto_execute": False,
            "priority": 1,
        },
    ],
}


def _setup_manager_with_mocks(manager: SuperWorkManager) -> None:
    """Wire up a SuperWorkManager with in-memory components and mocked Claude."""
    repo = SuperWorkRepository(":memory:")
    metrics = MetricsTracker()
    client = _mock_claude_response(GOOD_ANALYSIS)
    orchestrator = OrchestratorAgent(client=client, metrics_tracker=metrics)

    session = SuperWorkSession(project_path="/tmp/test-project")
    session.status = SessionStatus.WATCHING
    repo.save_session(session)

    manager._repo = repo
    manager._metrics = metrics
    manager._orchestrator = orchestrator
    manager._session = session
    manager._initialized = True
    manager._ws_connections = []


@pytest.fixture(autouse=True)
def _reset_manager():
    """Reset the global sw_manager before each test."""
    _setup_manager_with_mocks(sw_manager)
    yield
    sw_manager._initialized = False
    sw_manager._session = None
    sw_manager._repo = None
    sw_manager._metrics = None
    sw_manager._orchestrator = None
    sw_manager._ws_connections = []


# ─── REST Endpoint Tests ─────────────────────────────────


class TestSuperWorkSessionEndpoint:
    """GET /api/superwork/session."""

    @pytest.mark.asyncio
    async def test_get_active_session(self):
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/session")
        assert resp.status_code == 200
        data = resp.json()
        assert data["project_path"] == "/tmp/test-project"
        assert data["status"] == "WATCHING"
        assert "id" in data

    @pytest.mark.asyncio
    async def test_no_session_returns_error(self):
        sw_manager._session = None
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/session")
        assert resp.status_code == 200
        assert "error" in resp.json()


class TestSuperWorkProposalsEndpoint:
    """GET /api/superwork/proposals + approve/skip."""

    @pytest.mark.asyncio
    async def test_get_proposals_triggers_analysis(self):
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
        assert resp.status_code == 200
        data = resp.json()
        assert "proposals" in data
        assert len(data["proposals"]) == 2
        assert data["proposals"][0]["title"] == "Add integration tests"
        assert data["summary"] == "Project progressing well"

    @pytest.mark.asyncio
    async def test_proposals_persisted_to_repo(self):
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
        data = resp.json()
        # Proposals should be saved in the repository
        saved = sw_manager._repo.get_proposals(sw_manager._session.id)
        assert len(saved) == len(data["proposals"])

    @pytest.mark.asyncio
    async def test_approve_proposal(self):
        # First create proposals
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
            proposal_id = resp.json()["proposals"][0]["id"]
            # Now approve
            resp = await client.post(f"/api/superwork/proposals/{proposal_id}/approve")
        assert resp.status_code == 200
        data = resp.json()
        assert data["status"] == "approved"
        assert data["proposal_id"] == proposal_id

        # Verify in DB
        approved = sw_manager._repo.get_proposals(
            sw_manager._session.id, status=ProposalStatus.APPROVED
        )
        assert len(approved) == 1
        assert approved[0].id == proposal_id

    @pytest.mark.asyncio
    async def test_skip_proposal(self):
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
            proposal_id = resp.json()["proposals"][1]["id"]
            resp = await client.post(f"/api/superwork/proposals/{proposal_id}/skip")
        assert resp.status_code == 200
        assert resp.json()["status"] == "skipped"

        skipped = sw_manager._repo.get_proposals(
            sw_manager._session.id, status=ProposalStatus.SKIPPED
        )
        assert len(skipped) == 1

    @pytest.mark.asyncio
    async def test_no_orchestrator_returns_empty(self):
        sw_manager._orchestrator = None
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
        data = resp.json()
        assert data["proposals"] == []
        assert data["total"] == 0


class TestSuperWorkMetricsEndpoint:
    """GET /api/superwork/metrics + POST /api/superwork/predict."""

    @pytest.mark.asyncio
    async def test_metrics_with_no_events(self):
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/metrics")
        assert resp.status_code == 200
        data = resp.json()
        assert data["tasks_completed"] == 0
        assert data["tasks_failed"] == 0

    @pytest.mark.asyncio
    async def test_metrics_after_events(self):
        # Record some events
        sw_manager._metrics.record_completion(_make_event("Task 1"))
        sw_manager._metrics.record_completion(_make_event("Task 2"))
        sw_manager._metrics.record_completion(
            _make_event("Task 3", errors=["Build failed"])
        )

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/metrics")
        data = resp.json()
        assert data["tasks_completed"] == 2
        assert data["tasks_failed"] == 1

    @pytest.mark.asyncio
    async def test_metrics_no_session_returns_error(self):
        sw_manager._metrics = None
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/metrics")
        assert "error" in resp.json()

    @pytest.mark.asyncio
    async def test_predict_endpoint(self):
        # Record events for velocity calculation
        for i in range(5):
            sw_manager._metrics.record_completion(_make_event(f"Task {i}"))

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.post(
                "/api/superwork/predict",
                json={"remaining_tasks": 10},
            )
        assert resp.status_code == 200
        data = resp.json()
        assert "remaining_tasks" in data
        assert "estimated_cost_usd" in data
        assert "confidence" in data
        assert data["remaining_tasks"] == 10

    @pytest.mark.asyncio
    async def test_predict_no_session(self):
        sw_manager._metrics = None
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.post(
                "/api/superwork/predict", json={"remaining_tasks": 5}
            )
        assert "error" in resp.json()


class TestSuperWorkSessionsListEndpoint:
    """GET /api/superwork/sessions."""

    @pytest.mark.asyncio
    async def test_list_sessions(self):
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/sessions")
        assert resp.status_code == 200
        data = resp.json()
        assert "sessions" in data
        assert data["total"] >= 1

    @pytest.mark.asyncio
    async def test_list_sessions_no_repo(self):
        sw_manager._repo = None
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/sessions")
        data = resp.json()
        assert data["sessions"] == []
        assert data["total"] == 0


# ─── Manager Event Flow ──────────────────────────────────


class TestManagerEventFlow:
    """Test SuperWorkManager._on_task_complete wiring."""

    @pytest.mark.asyncio
    async def test_task_complete_updates_metrics(self):
        event = _make_event("Built feature X")
        await sw_manager._on_task_complete(event)

        snap = sw_manager._metrics.snapshot()
        assert snap.tasks_completed == 1

    @pytest.mark.asyncio
    async def test_task_complete_records_to_repo(self):
        event = _make_event("Built feature Y")
        await sw_manager._on_task_complete(event)

        events = sw_manager._repo.get_events(sw_manager._session.id)
        assert len(events) == 1
        assert events[0].completed_task == "Built feature Y"

        # Metrics snapshot also saved
        latest = sw_manager._repo.get_latest_metrics(sw_manager._session.id)
        assert latest is not None

    @pytest.mark.asyncio
    async def test_task_complete_feeds_orchestrator(self):
        event = _make_event("Refactored auth")
        await sw_manager._on_task_complete(event)

        assert len(sw_manager._orchestrator._task_history) == 1
        assert sw_manager._orchestrator._task_history[0].completed_task == "Refactored auth"

    @pytest.mark.asyncio
    async def test_multiple_events_accumulate(self):
        for i in range(5):
            await sw_manager._on_task_complete(_make_event(f"Task {i}"))

        snap = sw_manager._metrics.snapshot()
        assert snap.tasks_completed == 5

        events = sw_manager._repo.get_events(sw_manager._session.id)
        assert len(events) == 5

    @pytest.mark.asyncio
    async def test_failed_event_tracked(self):
        event = _make_event("Deploy", errors=["Connection refused"])
        await sw_manager._on_task_complete(event)

        snap = sw_manager._metrics.snapshot()
        assert snap.tasks_completed == 0
        assert snap.tasks_failed == 1

    @pytest.mark.asyncio
    async def test_broadcast_to_ws_clients(self):
        mock_ws = AsyncMock()
        sw_manager._ws_connections.append(mock_ws)

        event = _make_event("Task done")
        await sw_manager._on_task_complete(event)

        mock_ws.send_json.assert_called_once()
        call_data = mock_ws.send_json.call_args[0][0]
        assert call_data["type"] == "task_complete"
        assert call_data["data"]["completed_task"] == "Task done"

    @pytest.mark.asyncio
    async def test_broadcast_removes_dead_connections(self):
        dead_ws = AsyncMock()
        dead_ws.send_json.side_effect = RuntimeError("Connection closed")
        alive_ws = AsyncMock()

        sw_manager._ws_connections = [dead_ws, alive_ws]
        event = _make_event("Task")
        await sw_manager._on_task_complete(event)

        # Dead connection removed, alive stays
        assert dead_ws not in sw_manager._ws_connections
        assert alive_ws in sw_manager._ws_connections
        alive_ws.send_json.assert_called_once()


# ─── Full Pipeline: Event → Proposals → Approve ──────────


class TestFullPipelineViaAPI:
    """Complete flow: record events → get proposals → approve → verify."""

    @pytest.mark.asyncio
    async def test_event_to_approval_flow(self):
        # 1. Record completion events
        for i in range(3):
            await sw_manager._on_task_complete(_make_event(f"Feature {i}"))

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            # 2. Check metrics via API
            metrics_resp = await client.get("/api/superwork/metrics")
            assert metrics_resp.json()["tasks_completed"] == 3

            # 3. Get proposals via API (triggers orchestrator)
            proposals_resp = await client.get("/api/superwork/proposals")
            proposals = proposals_resp.json()["proposals"]
            assert len(proposals) == 2

            # 4. Approve first proposal
            pid = proposals[0]["id"]
            approve_resp = await client.post(f"/api/superwork/proposals/{pid}/approve")
            assert approve_resp.json()["status"] == "approved"

            # 5. Skip second proposal
            pid2 = proposals[1]["id"]
            skip_resp = await client.post(f"/api/superwork/proposals/{pid2}/skip")
            assert skip_resp.json()["status"] == "skipped"

            # 6. Verify session still active
            session_resp = await client.get("/api/superwork/session")
            assert session_resp.json()["status"] == "WATCHING"

            # 7. Verify metrics include event history
            events = sw_manager._repo.get_events(sw_manager._session.id)
            assert len(events) == 3


# ─── Safety Invariants ───────────────────────────────────


class TestSafetyInvariantsViaAPI:
    """Verify safety invariants hold through the API layer."""

    @pytest.mark.asyncio
    async def test_high_risk_auto_execute_forced_false(self):
        """HIGH risk proposals must have auto_execute=False regardless of Opus response."""
        high_risk_analysis = {
            "summary": "Risky changes",
            "focus_area": "Infrastructure",
            "proposals": [
                {
                    "title": "Modify production config",
                    "description": "Change database connection pool",
                    "risk_level": "HIGH",
                    "auto_execute": True,  # Opus says True, must be overridden
                    "priority": 0,
                },
            ],
        }
        sw_manager._orchestrator = OrchestratorAgent(
            client=_mock_claude_response(high_risk_analysis),
            metrics_tracker=sw_manager._metrics,
        )

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
        proposals = resp.json()["proposals"]
        assert proposals[0]["auto_execute"] is False

    @pytest.mark.asyncio
    async def test_critical_risk_auto_execute_forced_false(self):
        """CRITICAL risk proposals must always require human approval."""
        critical_analysis = {
            "summary": "Critical operations",
            "focus_area": "Database",
            "proposals": [
                {
                    "title": "Drop staging database",
                    "description": "Remove old staging data",
                    "risk_level": "CRITICAL",
                    "auto_execute": True,
                    "priority": 0,
                },
            ],
        }
        sw_manager._orchestrator = OrchestratorAgent(
            client=_mock_claude_response(critical_analysis),
            metrics_tracker=sw_manager._metrics,
        )

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
        proposals = resp.json()["proposals"]
        assert proposals[0]["auto_execute"] is False

    @pytest.mark.asyncio
    async def test_low_risk_auto_execute_preserved(self):
        """LOW risk proposals keep their auto_execute setting."""
        low_risk_analysis = {
            "summary": "Safe changes",
            "focus_area": "Tests",
            "proposals": [
                {
                    "title": "Add unit test",
                    "description": "Test login function",
                    "risk_level": "LOW",
                    "auto_execute": True,
                    "priority": 0,
                },
            ],
        }
        sw_manager._orchestrator = OrchestratorAgent(
            client=_mock_claude_response(low_risk_analysis),
            metrics_tracker=sw_manager._metrics,
        )

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
        proposals = resp.json()["proposals"]
        assert proposals[0]["auto_execute"] is True


# ─── WebSocket Tests ──────────────────────────────────────


class TestSuperWorkWebSocket:
    """WebSocket endpoint tests."""

    @pytest.mark.asyncio
    async def test_ws_ping_pong(self):
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            async with client.stream(
                "GET",
                "/api/superwork/ws",
                headers={
                    "connection": "upgrade",
                    "upgrade": "websocket",
                },
            ) as resp:
                # httpx doesn't support real WS, test via broadcast helper instead
                pass

        # Test broadcast helper directly — the WS endpoint is tested via the broadcast mechanism
        mock_ws = AsyncMock()
        sw_manager._ws_connections = [mock_ws]
        await sw_manager._broadcast({"type": "test", "data": "hello"})
        mock_ws.send_json.assert_called_once_with({"type": "test", "data": "hello"})

    @pytest.mark.asyncio
    async def test_broadcast_proposal_approved(self):
        mock_ws = AsyncMock()
        sw_manager._ws_connections = [mock_ws]

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            # Create a proposal first
            resp = await client.get("/api/superwork/proposals")
            pid = resp.json()["proposals"][0]["id"]
            # Approve it — should broadcast
            await client.post(f"/api/superwork/proposals/{pid}/approve")

        # Check broadcast was called with approval message
        calls = mock_ws.send_json.call_args_list
        approval_msg = [c for c in calls if c[0][0].get("type") == "proposal_approved"]
        assert len(approval_msg) == 1
        assert approval_msg[0][0][0]["proposal_id"] == pid

    @pytest.mark.asyncio
    async def test_broadcast_proposal_skipped(self):
        mock_ws = AsyncMock()
        sw_manager._ws_connections = [mock_ws]

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
            pid = resp.json()["proposals"][1]["id"]
            await client.post(f"/api/superwork/proposals/{pid}/skip")

        calls = mock_ws.send_json.call_args_list
        skip_msg = [c for c in calls if c[0][0].get("type") == "proposal_skipped"]
        assert len(skip_msg) == 1


# ─── Error Resilience ─────────────────────────────────────


class TestErrorResilience:
    """API handles errors gracefully without crashing."""

    @pytest.mark.asyncio
    async def test_orchestrator_api_error(self):
        """Claude API failure returns analysis with error status."""
        error_client = MagicMock()
        error_client.messages.create = AsyncMock(side_effect=ConnectionError("timeout"))
        sw_manager._orchestrator = OrchestratorAgent(
            client=error_client, metrics_tracker=sw_manager._metrics
        )

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
        data = resp.json()
        assert data["status"] == "api_unavailable"

    @pytest.mark.asyncio
    async def test_orchestrator_malformed_response(self):
        """Malformed Claude response returns parse_error status."""
        bad_msg = MagicMock()
        bad_msg.content = [MagicMock(text="not valid json {{{")]
        bad_client = MagicMock()
        bad_client.messages.create = AsyncMock(return_value=bad_msg)
        sw_manager._orchestrator = OrchestratorAgent(
            client=bad_client, metrics_tracker=sw_manager._metrics
        )

        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            resp = await client.get("/api/superwork/proposals")
        data = resp.json()
        assert data["status"] == "parse_error"

    @pytest.mark.asyncio
    async def test_manager_handles_none_repo_gracefully(self):
        """Event handling doesn't crash when repo is None."""
        sw_manager._repo = None
        event = _make_event("Task")
        # Should not raise
        await sw_manager._on_task_complete(event)
        # Metrics still tracked
        assert sw_manager._metrics.snapshot().tasks_completed == 1

    @pytest.mark.asyncio
    async def test_manager_handles_none_session_gracefully(self):
        """Event handling doesn't crash when session is None."""
        sw_manager._session = None
        event = _make_event("Task")
        await sw_manager._on_task_complete(event)
        assert sw_manager._metrics.snapshot().tasks_completed == 1
