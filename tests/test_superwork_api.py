"""Tests for SuperWork API routes."""

from unittest.mock import AsyncMock

import pytest

from kovrin.superwork.models import (
    MetricsSnapshot,
    PredictionResult,
    ProjectAnalysis,
    ProposalStatus,
    SuperWorkSession,
    TaskProposal,
)


class TestRouterImport:
    def test_import_router(self):
        from kovrin.api.superwork_router import router

        assert router is not None
        assert router.prefix == "/api/superwork"

    def test_import_manager(self):
        from kovrin.api.superwork_router import SuperWorkManager

        assert SuperWorkManager is not None


class TestSuperWorkManager:
    def test_initial_state(self):
        from kovrin.api.superwork_router import SuperWorkManager

        manager = SuperWorkManager()
        assert manager._session is None
        assert manager.is_initialized is False
        assert manager._ws_connections == []


class TestProposalModels:
    def test_approval_status_change(self):
        proposal = TaskProposal(title="T", description="D")
        assert proposal.status == ProposalStatus.PENDING
        updated = proposal.model_copy(update={"status": ProposalStatus.APPROVED})
        assert updated.status == ProposalStatus.APPROVED

    def test_skip_status_change(self):
        proposal = TaskProposal(title="T", description="D")
        updated = proposal.model_copy(update={"status": ProposalStatus.SKIPPED})
        assert updated.status == ProposalStatus.SKIPPED


class TestMetricsSerialization:
    def test_metrics_snapshot_serialization(self):
        snap = MetricsSnapshot(
            tasks_completed=10,
            tasks_failed=2,
            cost_usd=1.50,
            velocity_tasks_per_hour=5.0,
        )
        data = snap.model_dump()
        assert data["tasks_completed"] == 10
        assert data["cost_usd"] == 1.50
        assert "timestamp" in data


class TestPredictionSerialization:
    def test_prediction_serialization(self):
        pred = PredictionResult(
            remaining_tasks=5,
            estimated_hours=2.5,
            estimated_cost_usd=3.75,
            confidence=0.8,
        )
        data = pred.model_dump()
        assert data["remaining_tasks"] == 5
        assert data["confidence"] == 0.8


class TestSessionSerialization:
    def test_session_serialization(self):
        session = SuperWorkSession(project_path="/tmp/test")
        data = session.model_dump()
        assert data["project_path"] == "/tmp/test"
        assert data["status"] == "INITIALIZING"
        assert "id" in data


class TestAnalysisSerialization:
    def test_analysis_serialization(self):
        p = TaskProposal(title="Test", description="Desc")
        analysis = ProjectAnalysis(
            summary="All good",
            proposals=[p],
        )
        data = analysis.model_dump()
        assert data["summary"] == "All good"
        assert len(data["proposals"]) == 1


class TestWebSocketBroadcast:
    def test_ws_connections_list(self):
        from kovrin.api.superwork_router import SuperWorkManager

        manager = SuperWorkManager()
        assert manager._ws_connections == []

    @pytest.mark.asyncio
    async def test_broadcast_to_empty(self):
        from kovrin.api.superwork_router import SuperWorkManager

        manager = SuperWorkManager()
        await manager._broadcast({"type": "test"})

    @pytest.mark.asyncio
    async def test_broadcast_to_connections(self):
        from kovrin.api.superwork_router import SuperWorkManager

        manager = SuperWorkManager()
        mock_ws = AsyncMock()
        manager._ws_connections.append(mock_ws)
        await manager._broadcast({"type": "event", "data": "test"})
        mock_ws.send_json.assert_called_once_with({"type": "event", "data": "test"})

    @pytest.mark.asyncio
    async def test_broadcast_removes_disconnected(self):
        from kovrin.api.superwork_router import SuperWorkManager

        manager = SuperWorkManager()
        mock_ws = AsyncMock()
        mock_ws.send_json.side_effect = Exception("disconnected")
        manager._ws_connections.append(mock_ws)
        await manager._broadcast({"type": "test"})
        assert mock_ws not in manager._ws_connections
