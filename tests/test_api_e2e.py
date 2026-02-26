"""End-to-end tests for the Kovrin API server.

Tests REST endpoints, request validation, and response structure
using httpx ASGI transport (no running server needed).
"""

import pytest
from httpx import ASGITransport, AsyncClient

import kovrin.api.server as server
from kovrin.api.server import PipelineManager, RunRequest, StatusResponse, app
from kovrin.core.models import (
    AutonomyProfile,
    ExecutionResult,
    RiskLevel,
    RoutingAction,
    SubTask,
    Trace,
)


@pytest.fixture(autouse=True)
def _init_manager():
    """Initialize the PipelineManager so endpoints work without lifespan."""
    server.manager = PipelineManager()
    yield
    server.manager = None


# ─── Health & Status ─────────────────────────────────────────


class TestHealthAndStatus:
    """API health and status endpoints."""

    @pytest.mark.asyncio
    async def test_health_endpoint(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/health")
            assert response.status_code == 200
            data = response.json()
            assert data["status"] in ("ok", "degraded")

    @pytest.mark.asyncio
    async def test_status_endpoint(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/status")
            assert response.status_code == 200
            data = response.json()
            assert "version" in data
            assert data["version"] == "2.0.0a1"
            assert "running_pipelines" in data
            assert "completed_pipelines" in data

    @pytest.mark.asyncio
    async def test_status_response_model(self):
        """StatusResponse model validation."""
        sr = StatusResponse(
            running_pipelines=3,
            completed_pipelines=10,
        )
        assert sr.version == "2.0.0a1"
        assert sr.running_pipelines == 3


# ─── Traces Endpoint ─────────────────────────────────────────


class TestTracesEndpoint:
    """GET /api/traces/{intent_id} endpoint."""

    @pytest.mark.asyncio
    async def test_traces_not_found(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/traces/nonexistent-123")
            assert response.status_code == 200
            data = response.json()
            assert "error" in data

    @pytest.mark.asyncio
    async def test_traces_with_data(self):
        intent_id = "test-traces-e2e"
        traces = [
            Trace(intent_id=intent_id, event_type="INTENT_RECEIVED", description="Test"),
            Trace(intent_id=intent_id, event_type="DECOMPOSITION", description="Decomposed"),
        ]
        server.manager._results[intent_id] = ExecutionResult(
            intent_id=intent_id,
            output="Done",
            traces=traces,
        )

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get(f"/api/traces/{intent_id}")
            assert response.status_code == 200
            data = response.json()
            assert data["intent_id"] == intent_id
            assert data["total"] == 2
            assert len(data["traces"]) == 2


# ─── Graph Endpoint ──────────────────────────────────────────


class TestGraphEndpoint:
    """GET /api/graph/{intent_id} endpoint."""

    @pytest.mark.asyncio
    async def test_graph_not_found(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/graph/nope-123")
            assert response.status_code == 200
            data = response.json()
            assert "error" in data

    @pytest.mark.asyncio
    async def test_graph_with_data(self):
        intent_id = "test-graph-e2e"
        server.manager._results[intent_id] = ExecutionResult(
            intent_id=intent_id,
            graph_summary={
                "nodes": [
                    {"id": "t-1", "description": "Step 1", "deps": []},
                    {"id": "t-2", "description": "Step 2", "deps": ["t-1"]},
                ],
                "edges": [{"from": "t-1", "to": "t-2"}],
            },
        )

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get(f"/api/graph/{intent_id}")
            assert response.status_code == 200
            data = response.json()
            assert data["intent_id"] == intent_id
            assert "graph" in data
            assert len(data["graph"]["nodes"]) == 2


# ─── Result Endpoint ─────────────────────────────────────────


class TestResultEndpoint:
    """GET /api/result/{intent_id} endpoint."""

    @pytest.mark.asyncio
    async def test_result_not_found(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/result/missing-123")
            assert response.status_code == 200
            data = response.json()
            assert "error" in data

    @pytest.mark.asyncio
    async def test_result_success(self):
        intent_id = "test-result-e2e"
        server.manager._results[intent_id] = ExecutionResult(
            intent_id=intent_id,
            output="Analysis complete: costs reduced by 15%",
            success=True,
            sub_tasks=[
                SubTask(id="t-1", description="Analyze"),
                SubTask(id="t-2", description="Summarize"),
            ],
        )

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get(f"/api/result/{intent_id}")
            assert response.status_code == 200
            data = response.json()
            assert data["intent_id"] == intent_id
            assert data["success"] is True
            assert "15%" in data["output"]

    @pytest.mark.asyncio
    async def test_result_failure(self):
        intent_id = "test-result-fail-e2e"
        server.manager._results[intent_id] = ExecutionResult(
            intent_id=intent_id,
            output="All tasks rejected by safety critics",
            success=False,
            rejected_tasks=[SubTask(id="t-bad", description="Dangerous")],
        )

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get(f"/api/result/{intent_id}")
            assert response.status_code == 200
            data = response.json()
            assert data["success"] is False


# ─── Request Validation ──────────────────────────────────────


class TestRequestValidation:
    """RunRequest model validation."""

    def test_minimal_request(self):
        req = RunRequest(intent="Test")
        assert req.intent == "Test"
        assert req.constraints == []
        assert req.context == {}

    def test_full_request(self):
        req = RunRequest(
            intent="Analyze expenses",
            constraints=["No layoffs", "Focus on Q4"],
            context={"budget": 10000, "department": "Engineering"},
        )
        assert len(req.constraints) == 2
        assert req.context["budget"] == 10000


# ─── PipelineManager ────────────────────────────────────────


class TestPipelineManagerE2E:
    """PipelineManager state management."""

    def test_fresh_manager(self):
        pm = PipelineManager()
        status = pm.status
        assert status.running_pipelines == 0
        assert status.completed_pipelines == 0

    def test_result_storage_and_retrieval(self):
        pm = PipelineManager()

        # Store multiple results
        for i in range(5):
            pm._results[f"intent-{i}"] = ExecutionResult(
                intent_id=f"intent-{i}",
                output=f"Result {i}",
                success=True,
            )

        assert pm.get_result("intent-0") is not None
        assert pm.get_result("intent-4") is not None
        assert pm.get_result("intent-99") is None

    def test_result_attributes(self):
        pm = PipelineManager()
        result = ExecutionResult(
            intent_id="test",
            output="Done",
            success=True,
            sub_tasks=[SubTask(id="t-1", description="Work")],
        )
        pm._results["test"] = result

        loaded = pm.get_result("test")
        assert loaded.success is True
        assert len(loaded.sub_tasks) == 1


# ─── Safety Score Endpoint ───────────────────────────────────


class TestSafetyScoreEndpoint:
    """GET /api/safety-score endpoint."""

    @pytest.mark.asyncio
    async def test_safety_score_returns_data(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/safety-score")
            assert response.status_code == 200
            data = response.json()
            assert "overall_score" in data
            assert "components" in data
            components = data["components"]
            assert "constitutional" in components
            assert "audit" in components


# ─── Autonomy Endpoints ─────────────────────────────────────


class TestAutonomyEndpoints:
    """GET/POST /api/autonomy endpoint."""

    @pytest.mark.asyncio
    async def test_get_autonomy_settings(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/autonomy")
            assert response.status_code == 200
            data = response.json()
            assert "profile" in data

    @pytest.mark.asyncio
    async def test_update_autonomy_profile(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.post(
                "/api/autonomy",
                json={"profile": "CAUTIOUS"},
            )
            # Should succeed or return appropriate response
            assert response.status_code in (200, 422)


# ─── Pipelines Endpoint ─────────────────────────────────────


class TestPipelinesEndpoint:
    """GET /api/pipelines endpoint."""

    @pytest.mark.asyncio
    async def test_pipelines_returns_structure(self):
        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test",
        ) as client:
            response = await client.get("/api/pipelines")
            assert response.status_code == 200
            data = response.json()
            assert "pipelines" in data
            assert "total" in data
            assert isinstance(data["pipelines"], list)
